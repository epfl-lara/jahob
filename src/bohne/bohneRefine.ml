open Util
open Form
open FormUtil
open PrintForm
open BohneUtil
open BohnePred
open BohneProgram
open BohneRegion
open Ast
open Bf
open Bf_set
open BohneAbstraction
open CachedDecider
open BfCachedDecider


(* debug messages *)
let debug_module_code = Debug.register_debug_module "BohneRefine"
let debug_msg = Debug.debug_print_msg debug_module_code

let guard_marker = "__guard"

let is_guard_comment =
  let guard_regexp = Str.regexp (".*" ^ guard_marker) in
  fun c -> try Str.search_forward guard_regexp c 0 >= 0 with Not_found -> false

let mark_as_guard =
  let guard_counter = ref 0 in
  fun f ->
    let fs = split_conjuncts f in
    let cfs = 
      List.map (function 
	| App (Const Comment, [Const (StringConst s); _]) as f when is_guard_comment s -> f
	|  f -> 
	    incr guard_counter; 
	    mk_comment (Printf.sprintf "__guard_%d" !guard_counter) f)
	fs
    in mk_and cfs


let refine_total_dp_calls = ref 0 
let refine_cached_dp_calls = ref 0 
let refine_dp_time = ref 0. 

let decide = measured_decide refine_total_dp_calls refine_cached_dp_calls refine_dp_time

let decide_fast = measured_decide_fast refine_total_dp_calls refine_cached_dp_calls refine_dp_time

exception RealCounterexample of string

(* report counterexample *)
let report_counter_example is_real region trace last_wp (last_gc, orig_assn) = 
  if is_real || !Debug.debug_level > 0 && Debug.debug_is_on debug_module_code  then begin 
  if is_real then print_endline "\n\nCOUNTEREXAMPLE:\n"
  else print_endline "\n\nSPURIOUS COUNTEREXAMPLE:\n";
  print_endline "Error trace:\n";
  let prettify_form f =
    let f0 = normalize_form false f in
    let f1 = strip_types f0 in
    string_of_form (form_of_sequent (sequent_of_form (unlambda f1)))
  in
  let print_step region gc pp' =
    print_endline "Predicates:";
    List.iter (print_pred_decl stdout) (List.filter (inherits_to region.ppoint) region.preds);
    print_newline ();
    print_endline "Abstract state:";
    print_abs_states stdout ((* Bf_set.join *) region.absstates);
    print_newline ();
    print_endline "Transition:";
    print_command stdout region.ppoint (gc, pp')
  in
  let last_region = List.fold_left (fun region (region', _, _) ->
    let gc, _, _ = region'.parent in
    print_step region gc region'.ppoint; region') region trace
  in
  print_step last_region last_gc AstUtil.dummy_program_point;
  Printf.printf "Violated property:\n\n%s\n\n" (prettify_form orig_assn);
  if not is_real then 
    Printf.printf "Last violated weakest precondition:\n\n%s\n\n"
      (prettify_form last_wp)
  else raise (RealCounterexample "BohneCounterexample")
  end

(* skolemize universal quantifiers in antecedent *)
let rec skolemize f env skolem_consts =
  match f with 
  | App (Const And, fs) ->
      let fs', env', skolem_consts' =
	List.fold_left (fun (fs', env', skolem_consts') f ->
	  let f', env', skolem_consts' = skolemize f env' skolem_consts' in
	  f'::fs', env', skolem_consts') ([], env, skolem_consts) fs
      in App (Const And, fs'), env', skolem_consts'
  | Binder (Forall, [], f1) -> skolemize f1 env skolem_consts
  | Binder (Forall, (v,t) :: vts, f1) -> 
      let v1 = Util.fresh_name "v" in
      let f1r = nsubst [(v,mk_var v1)] f1 in (** can call nsubst on fresh v1 *)
      skolemize (Binder (Forall, vts, f1r)) ((v1, t) :: env) (v1 :: skolem_consts) 
  | App (Const Comment, [c; f]) ->
      let f', env', skolem_consts' = skolemize f env skolem_consts in 
      App (Const Comment, [c; f']), env', skolem_consts'
  | App (Const Impl as c, [f1; f2])
  | App (Const MetaImpl as c, [f1; f2]) ->
      let f2', env', skolem_consts' = skolemize f2 env skolem_consts in
      App (c, [f1; f2']), env', skolem_consts'
  | _ -> f, env, skolem_consts
 
(* try to eliminate subformulae that contain skolem constants *)
let elim_skolem_consts skolem_consts (asms, conc) =
  let rec elim submap asms1 asms2 = function
    | [] -> submap, asms1, asms2
    | f :: fs ->
	match normalize 2 f with
	| App (Const Seteq, [t1; t2])
	| App (Const Eq, [t1; t2]) ->
	    let fv_t1 = fv t1 in
	    let fv_t2 = fv t2 in
	    if Util.disjoint fv_t1 skolem_consts then
	      if not (Util.disjoint fv_t2 skolem_consts) then
		elim ((t2, t1) :: submap) (f :: asms1) asms2 fs
	      else elim submap asms1 (f :: asms2) fs
	    else if Util.disjoint fv_t2 skolem_consts then
	      elim ((t1, t2) :: submap) (f :: asms1) asms2 fs
	    else elim submap asms1 (f :: asms2) fs
	| _ -> elim submap asms1 (f :: asms2) fs
  in if skolem_consts = [] then (asms, conc) else
  let submap, asms1, asms2 = elim [] [] [] asms in
  (asms1 @ List.map (ngsubst submap) asms2, ngsubst submap conc)

(* simplify formula for predicate extraction *)
let simplify_form env0 skolem_consts f0 =
  let rec simplify = function
    | App (Var rtrancl, [f; t1; t2])
      when rtrancl = str_rtrancl && equal t1 t2 
      -> mk_true  
    | App (Const Eq, [TypedForm (Const (IntConst i1), _); TypedForm (Const (IntConst i2), _)]) -> 
	Const (BoolConst (i1 = i2))
    | App (Const Eq, [t1; t2]) 
    | App (Const GtEq, [t1; t2])
    | App (Const LtEq, [t1; t2])
    | App (Const Subseteq, [t1; t2])
    | App (Const Seteq, [t1; t2]) when equal t1 t2 -> mk_true
    | App (Const Eq, [Const (BoolConst b); f])
    | App (Const Eq, [f; Const (BoolConst b)]) ->
	if b then simplify f else smk_not (simplify f)
    | App (Const MetaAnd, fs) 
    | App (Const And, fs) -> 
	smk_and (List.map simplify fs)
    | App (Const Or, fs) -> 
	smk_or (List.map simplify fs)
    | App (Const Not, [f]) -> smk_not (simplify f)
    | App (Const Impl, [f1; f2]) 
    | App (Const MetaImpl, [f1; f2]) -> 
	smk_impl (simplify f1, simplify f2)
    | Binder (Forall, vs, f) ->
	smk_foralls (vs, simplify f)
    | Binder (Exists, vs, f) ->
	smk_exists (vs, simplify f)
    | App (Const Comment, [c; f]) ->
	App (Const Comment, [c; simplify f])
    | TypedForm (f, ty) -> TypedForm (simplify f, ty)
    | f -> f
  in
  let f = (* concretize_preds *) f0 in
  let sq = sequent_of_form f in
  let idents = List.map fst env0 in 
  let sq, _ = elim_free_vars true (difference (fv f) idents) sq in 
  (* let sq = elim_skolem_consts skolem_consts sq in *)
  let f1 = unlambda (form_of_sequent sq) in
  let f2, env = TypeReconstruct.reconstruct_types env0 f1 in
  let f3, env1 = 
    TermRewrite.rewrite true 
      [TermRewrite.rewrite_tree]
      env (TypeReconstruct.disambiguate f2)
  in
  let f4, env2 = 
    TermRewrite.rewrite true
      [TermRewrite.rewrite_FieldRead_FieldWrite;
       TermRewrite.rewrite_sets] 
      env1 (rewrite_upd_rtrancl f3)
  in
  simplify (elim_quants f4), env2

(** Extracts predicates from a formula *)
let extract_preds env0 skolem_consts0 (f0 : form) =
  let f1, env1 = simplify_form env0 skolem_consts0 f0 in
  let f2, env2, skolem_consts = skolemize f1 env1 skolem_consts0 in
  let f, env = TypeReconstruct.reconstruct_types env2 f2 in
  let freshv, aux_env0 = 
    match Util.intersect skolem_consts0 (fv f) with
    | v :: _ -> v, []
    | _ -> let v = Util.fresh_name "v" in
      v, [(v, mk_object_type)]
  in
  let idents = List.map fst env0 in
  let rec atoms is_guard aux_env acc = function
    | App (Const Not, fs)
    | App (Const Or, fs)
    | App (Const And, fs)
    | App (Const MetaAnd, fs)
    | App (Const Impl, fs) 
    | App (Const MetaImpl, fs)
    | App (Const Iff, fs) ->
	List.fold_left (uncurry (atoms is_guard)) (aux_env, acc) fs
    | App (Const Comment, [Const StringConst c; f0]) ->
	atoms (is_guard (* || is_guard_comment c *)) aux_env acc f0
    | TypedForm (f0, _) -> atoms is_guard aux_env acc f0
    | App (Const Eq, [TypedForm (Var v1, ty); TypedForm (Var v2, _)]) 
      when ty = mk_object_type && List.mem v1 idents && List.mem v2 idents ->  
	let new_atoms = 
	  (if List.mem v1 idents then 
	    [mk_eq (TypedForm (Var v1, ty), TypedForm (Var freshv, ty))]
	  else []) @
	  (if List.mem v2 idents then 
	    [mk_eq (TypedForm (Var v2, ty), TypedForm (Var freshv, ty))]
	  else [])
	in aux_env, new_atoms @ acc
    | App (Const Eq, [TypedForm (t1, ty); TypedForm (t2, _)]) 
      when ty = mk_object_type
	  && empty (intersect (union (fv t1) (fv t2)) (skolem_consts @ List.map fst aux_env))
      -> aux_env, mk_eq (TypedForm (t1, ty), TypedForm (Var freshv, ty)) ::
	mk_eq (TypedForm (t2, ty), TypedForm (Var freshv, ty)) :: acc
    | App (Var rtrancl, [f; t1; t2]) when rtrancl = str_rtrancl && 
	empty (intersect (union (fv t1) (fv t2)) (skolem_consts @ List.map fst aux_env)) ->
	  aux_env, App (Var rtrancl, [f; t1; Var freshv]) ::
	  mk_eq (t2, Var freshv) :: acc
    | Binder (Forall, [(v,ty)], f) 
    | Binder (Exists, [(v,ty)], f) when ty = mk_object_type ->
	let v0 = Util.fresh_name "v" in
	atoms is_guard ((v0,ty) :: aux_env) acc (subst [(v, mk_var v0)] f) 
    | f ->
	if is_guard || 
	safe_unsome false (Decider.test_valid ([], f)) || 
	safe_unsome false (Decider.test_valid ([f], mk_false)) ||
	List.exists (equal f) acc then aux_env, acc else aux_env, f::acc
  in 
  let aux_env, atoms_f = atoms false aux_env0 [] f in
  List.map fst aux_env @ skolem_consts, 
  aux_env @ env, atoms_f, f
      
(* generate new predicates from formulas [atoms] with potential free variables in [free_vs] *)
let preds_from_atoms ?(inherited_pps=[]) unify_iters vardefs idents ghost_vs free_vs env atoms =
  let has_obj_type v =
    try
      List.assoc v env = mk_object_type 
    with Not_found -> false
  in
  let filter_obj_vs = List.filter has_obj_type in 
  let obj_free_vs = filter_obj_vs free_vs in
  let get_free_vs p = 
    Util.difference (fv p) 
      (Util.difference idents obj_free_vs)
  in
  let unify_atoms atoms other_atoms =
    let unifiable_vs = filter_obj_vs (get_free_vs (mk_list atoms)) in
    let filter_mgu mgu = 
      List.filter 
	(function (_, Var x) -> not (List.mem x unifiable_vs) | _ -> true)
	mgu
    in
    let rec unify acc = function
      |	0 -> fun _ -> acc
      |	n -> function
	  | [] -> unify acc (n - 1) (acc @ atoms) 
	  | a::rest ->
	      let acc' = 
		List.fold_left 
		  (fun acc b ->
		    let unifiable, mgu = is_unifiable [] unifiable_vs a b in
		    let mgu' = filter_mgu mgu in
		    if unifiable && mgu' <> [] then 
		      union (difference (List.map (subst mgu') atoms) atoms) acc
		    else acc) acc (rest @ other_atoms)
	      in unify acc' n rest
    in unify [] unify_iters atoms
  in 
  let pred_from_atom rel_vs =
    let rel_tvs = List.map (fun v -> (v, mk_object_type)) rel_vs in
    fun (preds, rest) p ->
    match get_free_vs p with
    | [] when not (is_oldform free_vs p) -> 
        (* state predicate *)
	let ps =
	  try
	    let aux_preds, pred = form_to_preds [] p in
	    union_preds [pred] aux_preds
	  with Not_found -> [add_pred p [Inherit inherited_pps]]
	in
	union_preds ps preds, rest
    | vs when List.for_all has_obj_type vs ->
	(* unary predicate on objects *)
	let props, aux_preds =
	  (*let aux_preds0 = match unnotate_all_types p with
	  | App (Const Eq, [App (Var fld1, [App (Var fld2, [t])]); Var v1]) when
	      v1 = v
	    ->
	      let fields = if fld1 = fld2 then [Var fld1] else [Var fld1; Var fld2] in
	      let aux_def = 
		Binder (Comprehension, [(v, mk_object_type)], App (mk_rtrancl_pt fields, [t; Var v]))
	      in
	      [add_pred aux_def [Inherit inherited_pps]]
	  | p -> []	      
	  in*)
	  let props0 = [Inherit inherited_pps] in
	  if is_oldform (vs @ ghost_vs) p then
	    let aux_pred =
	      let p1, _ = TypeReconstruct.reconstruct_types env (unlambda (subst vardefs (remove_old p))) in
	      let p1_def = Binder (Comprehension, rel_tvs, p1) in
	      try
		let p1, _ = TypeReconstruct.reconstruct_types env (unlambda (remove_old p)) in
		match vs, p1 with
		| [_], App (Const Elem, [_; TypedForm (Var v, _)])
		| [_], App (Const Elem, [_; Var v]) -> pred_by_name v
		| _ -> 
		    add_pred p1_def  [Inherit inherited_pps]
	      with Not_found ->
		add_pred p1_def  [Inherit inherited_pps]
		
	    in
	    (IsOld aux_pred.pred_name :: IsConst :: props0), [aux_pred]
	  else props0, []
	in
	let p_def = Binder (Comprehension, rel_tvs, p) in
	let res = union_preds (union_preds [add_pred p_def props] aux_preds) preds, rest in
	res
    | _ -> preds, p :: rest
  in 
  (* let atoms = List.sort (fun p q -> compare (List.length (get_free_vs q)) (List.length (get_free_vs p))) atoms in *)
  let rel_vs = List.fold_left (fun rel_vs a ->
    Util.union (get_free_vs a) rel_vs) [] atoms
  in
  (* let _ = List.iter (print_form) atoms in
  let _ = List.iter (Printf.printf "%s, ") rel_vs in *)
  let preds0, rest = List.fold_left (pred_from_atom rel_vs) ([], []) atoms in
  let rest' = unify_atoms rest (difference atoms rest) in
  let preds, _ = List.fold_left (pred_from_atom rel_vs) (preds0, []) rest' in
  preds

let refine prog root_region region f0 skolem_consts_env refine_absinv =
  (* remove type information from skolem constants *)
  let skolem_consts0 = List.map fst skolem_consts_env in
  (* extract atomic formulae from f *)
  let skolem_consts, env, atoms, f = extract_preds prog.global_env skolem_consts0 f0 in
  (* generate predicates from atoms *)
  let _ = debug_msg 1 (fun chan ->
    Printf.fprintf chan "\nRefining region %d for pp. %d with:\n" region.timestamp region.ppoint.pp_id;
    output_string chan (string_of_sequent (sequent_of_form f) ^ "\n"))
  in
  let _, _, parent_region = root_region.parent in 
  let unify_iters =    
    (* if region_equal !parent_region region then 0 else 3 *) 0
  in
  let gen_preds = preds_from_atoms ~inherited_pps:[region.ppoint] unify_iters 
      prog.vardefs prog.idents [] skolem_consts env atoms 
  in
  let new_preds = diff_preds gen_preds (List.filter (fun p -> not (inherits p) || inherits_to region.ppoint p) region.preds) in
  let _ = debug_msg 1 (fun chan -> 
    if new_preds <> [] then begin
      output_string chan "Adding predicates:\n";    
      List.iter (fun p -> print_pred_decl chan p) new_preds
    end else
      output_string chan "No new predicates discovered.\n")
  in
  (* update abstract invariant of region *)
  let abs_f = 
    if !BohneOptions.opt_refine_progress then 
      fast_alpha (union_preds region.preds gen_preds) skolem_consts f
    else Bf_set.top
  in  
  let old_absinvariant = region.absinvariant in
  let _ = if !BohneOptions.opt_refine_progress && refine_absinv (* && new_preds = []  && region_equal region !parent_region *) then
    let _ = debug_msg 3 (fun chan ->
      output_string chan "Abstract invariant:\n";
      print_abs_states chan abs_f)
    in
    let _ = if !BohneOptions.opt_check_soundness then
      let tobechecked = smk_impl (smk_foralls (skolem_consts_env, f), gamma false (union_preds region.preds gen_preds) abs_f) in
      assert (entails trivial_context (smk_and region.invariant) tobechecked)
    in
    region.absinvariant <- Bf_set.inter old_absinvariant abs_f
  in
  let is_refined = new_preds <> [] || 
  (region_equal region root_region || region_equal region !parent_region) &&
  not (Bf_set.eq region.absinvariant old_absinvariant) &&
  !BohneOptions.opt_refine_progress 
  in
  is_refined, gen_preds

let minimize_antecedent decide f =
  let ante, succ = sequent_of_form f in
  let rec check acc = function
    | [] -> 
	form_of_sequent (acc, succ)
    | a :: rest ->
	if decide (form_of_sequent (acc @ rest, succ)) then
	  check acc rest
	else check (a :: acc) rest
  in check [] ante

let extract_useful_guards useful_guards f =
  let is_useful c =
    try 
      if Str.search_forward (Str.regexp "__guard_[0-9]+") c 0 >= 0 then
	let g = Str.matched_string c in
	Str.search_forward (Str.regexp_string g) useful_guards 0 >= 0
      else false
    with Not_found -> false
  in
  let ante, succ = sequent_of_form f in
  let ante' = List.fold_left
      (fun acc -> function 
	| App (Const Comment, [Const (StringConst s); _]) 
	  when not (is_useful s) -> acc
	| f -> f :: acc) 
      [] ante
  in form_of_sequent (ante', succ)
	    

(* try to factorize a conjunct from a disjunction of conjunctions to improve
   splitting into proof subgoals.
   e.g. (A & B | ~A & C | ~A | D)) becomes (A --> B) & (~A --> C | D) *)
let factorize disj =
  let rec conjuncts d =
    match d with
    | App (Const And, fs)
    | App (Const MetaAnd, fs) -> List.concat (List.rev_map conjuncts fs)
    | App (Const Not, [App (Const Or, fs)]) -> List.concat (List.rev_map (fun f -> conjuncts (smk_not f)) fs) 
    | _ -> [d]
  in
  match disj with
  | d :: disj' ->
      (try find_map (fun f ->
	try let pos, neg = 
	  List.fold_left (fun (pos, neg) d ->
	    let cs, kind = List.fold_left 
		(fun (cs, kind) c -> 
		  if equal f c then (cs, Some true)
		  else if equal f (smk_not c) then (cs, Some false)
		  else (c::cs, kind)) ([], None) (conjuncts d)
	    in match kind with
	    | Some true -> (smk_and cs::pos, neg)
	    | Some false -> (pos, smk_and cs::neg)
	    | None -> raise Not_found) ([], []) disj
	in Some [smk_impl (f, smk_or pos); smk_impl (smk_not f, smk_or neg)]
	with Not_found -> None)
	  (conjuncts d)
      with Not_found -> [smk_or disj])
  | _ -> [smk_or disj]

(* check assertions and analyze potential counter-examples *)
let check_assertions program region assns =
  let rec analyze region trace skolem_consts assns =
    let mk_context abs_states f =
      let preds = List.filter (fun p -> is_relevant f p || is_old p) region.preds in
      let region_join = Bf_set.join abs_states in
      (region_join, concretize_invariant preds)
    in
    let inv = smk_and region.invariant in
    
    (* recursively split violated assertions to find a smallest violated subformula *)
    let rec check_and_split skolem_consts acc = function
      | [] -> skolem_consts, List.rev acc
      | (src_states, wp_assn, orig_assn) :: todo ->
	  (* let _ = print_abs_states stdout src_states in *)
	  let check_assn skolem_consts abs_states assn =
	    let other_assns = List.map (fun (_, assn, _) -> smk_foralls (skolem_consts, assn)) acc in
	    let context = mk_context abs_states assn in
	    let assn = 
	      if !BohneOptions.opt_abstract_final then
		let old_invs = 
		  concretize_old_invariant region.preds (Bf_set.join abs_states)
		in
		smk_impl (smk_and old_invs, assn)
	      else assn
	    in
	    let checked_form =
	      if is_root region then 
		let concr_assn = subst program.vardefs (remove_old assn) in
		let pre_cond = smk_and 
		    (snd context (fst context) :: inv :: 
		     List.map (subst program.vardefs) other_assns)
		in
		smk_impl (pre_cond, concr_assn)
	      else smk_impl (smk_and (inv::other_assns), assn)
	    in
	    let res = 
	      (* decide (Bf_set.join abs_states, stack_context region.preds) checked_form || *)
	      decide context checked_form
	    in
	    res
	  in
	  (* ToDo: implement some sort of binary search for splitting on abstract states *)
	  let split_on_states skolem_consts' assn =
	    if Bf_set.le (Bf_set.singleton (Bf_set.join region.absstates)) src_states then 
	      let acc' = (src_states, assn, orig_assn) :: acc in
	      check_and_split skolem_consts' acc' [] (* todo *)
	    else 
	      let src_states', assn_holds = 
		Bf_set.fold 
		  (fun (src_states', res as acc) abs_state -> 
		    if not res then acc else 
		    Bf_set.singleton abs_state, 
		    res && check_assn skolem_consts' (Bf_set.singleton abs_state) assn)
		  (src_states, true) src_states
	      in 
	      if assn_holds then check_and_split skolem_consts' acc todo
	      else 
		let acc' = (src_states', assn, orig_assn) :: acc in
		check_and_split skolem_consts' acc' [] (* todo *)
	  in

	  let _ = debug_msg 1 (fun chan -> 
	    if trace = [] then begin
	      output_string chan "\nChecking assertion: ";
	      (match orig_assn with
	      |	(_, App (Const Comment, [Const (StringConst c); _]))
	      |	(_, App (Const Impl, [_; App (Const Comment, [Const (StringConst c); _])])) -> 
		  output_string chan c
	      |	(_, f) -> output_string chan ("\n" ^ string_of_form (strip_types f)));
	      output_string chan "\n"; 
	      flush chan
	    end)
	  in

	  (* check wether assertion [wp_assn] holds in [src_states] and continue with [todo] *)
	  if check_assn skolem_consts src_states wp_assn then begin
	    let _ = debug_msg 1 (fun chan -> 
	      if trace = [] then output_string chan "Assertion verifies.\n")
	    in
	    check_and_split skolem_consts acc todo
	  end else
          (* otherwise try to split wp_assn into smaller subformulae *) 
	  let env = 
	    TypeReconstruct.get_env 
	      (form_of_sequent ([concretize_invariant region.preds Bf.top; inv], wp_assn)) 
	  in
	  let split_assn2, _ = 
	    TermRewrite.rewrite true 
	      [TermRewrite.rewrite_tree] env (TypeReconstruct.disambiguate (unlambda wp_assn))
	  in
	  let split_assn1, _ = 
	    TermRewrite.rewrite true 
	      [TermRewrite.rewrite_FieldRead_FieldWrite] env (rewrite_upd_rtrancl split_assn2)
	  in
	  let split_assns0 = Decider.generate_sequents [] (elim_quants split_assn1) in
	  let skolem_consts', split_assns = 
	    List.fold_left 
	      (fun (skolem_consts', split_assns) ((asms, hyp), env) ->
		let skolem_consts' = env @ skolem_consts' in
		let hyp', _ =  TermRewrite.rewrite true [TermRewrite.rewrite_sets] skolem_consts' hyp in
		skolem_consts', smk_impl (smk_and asms, elim_quants hyp') :: split_assns) 
	      (skolem_consts, []) split_assns0 
	  in
	  match split_assns with
	  | [f] ->
	      (match f with
	      | App (Const MetaImpl, [f;f1]) 
	      | App (Const Impl, [f;f1]) ->
		  (match f1 with 
		  | App (Const Or, disj)
		  | App (Const Comment, [_; App(Const Or, disj)]) ->
		      (match factorize disj with
		      | [_] -> split_on_states skolem_consts' (smk_impl (f, f1))
		      | assns' ->  
			  let todo' = 
			    List.rev_map (fun assn -> (src_states, smk_impl (f, assn), orig_assn)) assns' @ todo 
			  in check_and_split skolem_consts' acc todo')
		  | App (Const Iff, [f11; f12])
		  | App (Const Comment, [_; App(Const Iff, [f11; f12])]) ->
		      let todo' = 
			(src_states, smk_impl (smk_and [f; f11], f12), orig_assn) :: 
			(src_states, smk_impl (smk_and [f; f12], f11), orig_assn) :: todo
		      in
		      check_and_split skolem_consts' acc todo'
		  | App (Const And, assns') 
		  | App (Const Comment, [_; App(Const And, assns')]) ->
		      let todo' = 
			List.rev_map 
			  (fun assn -> (src_states, smk_impl (f, assn), orig_assn)) assns' @ todo 
		      in check_and_split skolem_consts' acc todo'
		  | App (Const Not, [App (Const Or, assns')])
		  | App (Const Comment, [_; App (Const Not, [App(Const Or, assns')])]) ->
		      let todo' = 
			List.rev_map 
			  (fun assn -> (src_states, smk_impl (f, smk_not assn), orig_assn)) assns' @ todo 
		      in check_and_split skolem_consts' acc todo'
		  | App (Const Not, [App (Const And, f2::fs)])
		  | App (Const Comment, [_; App (Const Not, [App(Const And, f2::fs)])]) ->
		      let todo' = (src_states, smk_impl (smk_and [f;f2], smk_not (smk_and fs)), orig_assn) :: todo in
		      check_and_split skolem_consts' acc todo'
 		  | _ -> 
		      (match f with 
		      |	App (Const And, fs)
		      |	App (Const MetaAnd, fs) ->
			  let f_opt, fs_rest = List.fold_left 
			      (function 
				| (None, acc) ->
				    (function 
				      |	App (Const Or, gs) 
				      |	App (Const Comment, [_; App (Const Or, gs)]) ->
					  (Some gs, acc)
				      |	g -> (None, g :: acc))
				| (f_opt, acc) -> 
				    fun g -> (f_opt, g :: acc)
			      ) (None, []) fs
			  in (match f_opt with
			  | Some gs ->
			      let todo' = 
				List.rev_map (fun g -> (src_states, smk_impl (smk_and (g :: fs_rest), f1), orig_assn)) gs @ todo
			      in		      
			      check_and_split skolem_consts' acc todo'
			  | None -> 
			      split_on_states skolem_consts' (smk_impl (f, f1)))
		      |	_ -> split_on_states skolem_consts' (smk_impl (f, f1))))
	      | _ -> split_on_states skolem_consts' f)
	  | _ -> 
	      let todo' = List.rev_map (fun assn -> (src_states, assn, orig_assn)) split_assns @ todo in
	      check_and_split skolem_consts' acc todo'
    in
    let get_next_gc orig_assn =
      match trace with
      | (next_region, _, _) :: _ -> 
	  let gc, _, _ = next_region.parent in gc
      | [] -> fst orig_assn
    in   
    let mk_wp gc f = 
      let wp_f0 = smk_impl (mark_as_guard (remove_comments gc.gc_guard), program.wp gc.gc_command f) in
      let fv_before_havoc = get_annotated_types wp_f0 in
      let wp_f = program.wp (project_gc_havoc gc) wp_f0 in
      Util.difference (get_annotated_types wp_f) fv_before_havoc, wp_f
    in
    let _, parent_src_states, parent_region = region.parent in 
    let skolem_consts', wp_assns = 
      List.fold_right (fun (src_states, assn, orig_assn) (skolem_consts', wp_assns) -> 
	let next_gc = get_next_gc orig_assn in
	let havoced_vs, wp_assn = mk_wp next_gc assn in
	havoced_vs @ skolem_consts', (src_states, wp_assn, orig_assn) :: wp_assns) 
	assns (skolem_consts, [])
    in
    let skolem_consts', assns' = check_and_split skolem_consts' [] wp_assns in
    let mk_parent_assn acc (src_states, assn, orig_assn) =
      (* assertion [assn] is violated in current region *)
      debug_msg 3 (fun chan ->
	let context = mk_context src_states assn in
	Printf.fprintf chan 
	  "\nViolated formula at location %d:\n%s" 
	  region.ppoint.pp_id
	  (string_of_form 
	     (form_of_sequent 
		(sequent_of_form 
		   (form_of_sequent ([snd context (fst context); inv], assn)))) ^ "\n"));
      if is_root region then 
	if !BohneOptions.opt_complete_prover then
          (* found real counter-example *)
	  (report_counter_example true region trace assn orig_assn; acc)
	else 
	  (* provers are incomplete - let's try with more predicates *)
	  acc
      else (* continue analysis with parent region *)
	(parent_src_states, assn, orig_assn) :: acc
    in
    let parent_assns = List.fold_left mk_parent_assn [] assns' in

    match parent_assns with
    | [] -> 
        (* no assertion is violated in current region *)
	(match trace with
	| [] -> 
            (* empty error trace, i.e. all assertions verify *)
	    None
	| (root_region, _, _) :: _ -> 
	    (* spurious part of trace starts from current region *)
            (* refine region [refined_region] *)
	    let refine_with_assn refined_region skolem_consts 
		(useful_guards, has_new, new_preds, new_inherited) (src_states, assn, orig_assn) =
	      let gc = get_next_gc orig_assn in
	      let first = refined_region.timestamp = root_region.timestamp in
	      let useful_guards, min_assn = 
		if first then begin
		  report_counter_example false region trace assn orig_assn;
		  let skolem_consts0 = List.map fst skolem_consts in
		  let simp_assn, _ = simplify_form program.global_env skolem_consts0 assn in
		  let min_assn = minimize_antecedent 
		      (fun f -> 
			let wp_f = program.wp (gc_to_basic_commands gc) f in
			let checked_form = smk_impl (inv, wp_f) in
			decide (mk_context src_states wp_f) checked_form) simp_assn
		  in
		  extract_comments min_assn, min_assn
		end else useful_guards, extract_useful_guards useful_guards assn
	      in
	      (* TODO: check why containers/hobgsll/List.java#reverse diverges with 'false' *)
	      let has_new', gen_preds = refine program root_region refined_region min_assn skolem_consts false in
	      let new_preds' = if first then union new_preds gen_preds else new_preds in
	      let new_inherited' = union_preds gen_preds new_inherited in
	      let parent_refined = first && !BohneOptions.opt_refine_progress && not has_new' && 
		let _, src_states, parent_ref = refined_region.parent in
		let parent_region = !parent_ref in
		let is_refined, new_parent_preds = 
		  let havoced_vars, wp_assn = mk_wp gc min_assn in
		  (* let min_assn = minimize_antecedent
		      (fun f ->
			let checked_form = smk_impl (inv, f) in
			decide (mk_context src_states f) checked_form) wp_assn
		  in *)
		  refine program root_region parent_region wp_assn (havoced_vars @ skolem_consts) true
		in
		let _ = parent_region.preds <- union_preds parent_region.preds new_parent_preds in
		is_refined	       
	      in
	      let this_refined = 
		let proto_refined = parent_refined || has_new || has_new' in
		proto_refined || 
		(first &&
		 let is_refined, _ = refine program root_region refined_region min_assn skolem_consts true in
		 is_refined)
	      in
	      useful_guards, this_refined, new_preds', new_inherited'
	    in
	    let _, has_new, new_preds, new_inherited = 
	      List.fold_left 
		(fun (useful_guards, has_new, new_preds, new_inherited) (region, assns, skolem_consts) ->
		  List.fold_left 
		    (refine_with_assn region skolem_consts) 
		    (useful_guards, has_new, new_preds, new_inherited) assns) 
		("", false, [], []) trace
	    in
            Some (root_region, has_new, new_preds, new_inherited))
    | parent_assns ->
        (* some assertions are violated in current region *)	   
        (* continue analysis with parent region *)
	analyze !parent_region ((region, parent_assns, skolem_consts') :: trace) skolem_consts' parent_assns      
  in 
  analyze region [] [] assns
      

(* count maximal number of quantified variables in the same scope *)
let count_max_bound =
  let add xs (x, _) = if List.mem x xs then xs else x::xs in
  let rec count bound old_max = function
    | App (Const Or, fs)
    | App (Const And, fs)
    | App (Const MetaAnd, fs)
    | App (Const Comment, Const StringConst _::fs)
    | App (Const Impl, fs) 
    | App (Const MetaImpl, fs)
    | App (Const Not, fs)
    | App (Const Iff, fs) ->
	List.fold_left (count bound) old_max fs
    | TypedForm (f1, _) -> count bound old_max f1
    | Binder (Forall, vs, f1)
    | Binder (Exists, vs, f1) ->
	count (List.fold_left add bound vs) old_max f1
    | _ -> max old_max (List.length bound)
  in count [] 0
  

(** Check assertions for region [region] *)
let check program region =
  if not !BohneOptions.opt_refine then None else
  let loc = get_location program region.ppoint in
  let exit_loc = get_location program program.exit_point in
  let postconds gc1 = 
    List.map (fun (gc2, f) -> (region.absstates, f, (compose program gc1 gc2, f)))
      exit_loc.loc_assertions 
  in  
  let checked_region, vcs = 
    if not (is_exit_pp program region.ppoint) then
      let vcs =
	List.fold_left 
	  (fun assertions (gc, succ_pp) ->
	    if is_exit_pp program succ_pp && not !BohneOptions.opt_abstract_final
	    then assertions @ postconds gc else assertions)
	  (List.map (fun (gc, f) -> (region.absstates, f, (gc, f))) loc.loc_assertions) loc.loc_cmds
      in
      region, vcs
    else
      let gc1, src_states, parent_ref = region.parent in
      let exit_invariant = 
	let preds = union_preds [null_decl] exit_loc.loc_preds in
	let old_invs = 
	  if !BohneOptions.opt_context_per_state then
	    Bf_set.fold (fun acc abs_state ->
	      smk_and (concretize_old_invariant region.preds abs_state) :: acc) [] region.absstates
	  else
	    [smk_and (concretize_old_invariant region.preds (Bf_set.join region.absstates))]
	in
	let sub = List.map (fun p -> (p.pred_name, p.pred_def)) preds in
	List.map (fun old_inv -> subst sub old_inv) old_invs
        (* smk_and (concretize_invariant preds (Bf_set.join region.absstates) ::
		 concretize_old_invariant preds (Bf_set.join region.absstates)) *)
      in
      let vcs = 
	List.fold_left (fun acc exit_inv ->
	  List.fold_right (fun (gc2, f) acc -> 
	    (src_states, smk_impl (mark_as_guard exit_inv, f), (compose program gc1 gc2, f)) :: acc) 
	    exit_loc.loc_assertions acc) [] exit_invariant
      in !parent_ref, vcs
  in
  let split_vcs = 
    List.concat (List.map (fun (r, f, oa) ->
      List.map (fun f -> (r, f, oa)) (split_conjuncts (subst program.vardefs f))) vcs)
  in
  (* let split_vcs = 
   List.concat (List.map (fun (r, c, f) ->
      Bf_set.fold (fun acc abs_state -> (Bf_set.singleton abs_state, c, f)::acc) [] r) split_vcs0)
  in *)
  (* heuristic: sort properties increasingly wrt. the max. number of universally quantified variables in the same scope *)
  let sorted_vcs =
    let extended = List.rev_map (fun (_, _, (_, f) as a) ->
      (a, count_max_bound (fst (simplify_form program.global_env [] f)))) split_vcs in
    let sorted = List.stable_sort (fun (_, c1) (_, c2) -> compare c1 c2) extended in
    List.map fst sorted
  in 
  check_assertions 
    program 
    checked_region 
    sorted_vcs
