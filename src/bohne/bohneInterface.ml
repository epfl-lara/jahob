open Util
open Ast
open AstUtil
open Form
open FormUtil
open PrintForm
open Sast
open Vcgen
open BohneUtil
open BohnePred
open BohneProgram
open BohneRegion
open BohneAbstraction
open Bohne


(** Find program point of command *) 
let find_program_point exit_point c =
  let rec find_in_list cs =
      List.fold_left (fun acc c ->
	if acc = exit_point then find c else acc)
	exit_point cs
  and find c = 
    match c with 
    | Basic bc -> bc.bcell_point
    | Seq cs | Choice cs -> find_in_list cs
    | If ic -> find_in_list [ic.if_then; ic.if_else]
    | Loop lc -> find_in_list [lc.loop_prebody; lc.loop_postbody]
    | PickAny pc -> find_in_list pc.pa_body
    | PickWitness pw -> find_in_list pw.pw_body
    | Assuming ac -> find_in_list ac.assuming_body
    | Induct ic -> find_in_list ic.induct_body
    | Contradict cc -> find_in_list cc.contradict_body
    | Proof pc -> find_in_list pc.proof_body
    | Return _ -> exit_point
  in find c


(** Identify candidate loop invariants which would be useful for the 
   synthesis (currently tree and field constraints) *)
let find_candidate_invariants pre_cond =
  let pres = split_conjuncts pre_cond in
  List.fold_left 
    (fun (pre_cond', helper_invs) f ->
      if is_tree_constraint f || is_field_constraint f 
      then (pre_cond', f::helper_invs)
      else (f::pre_cond', helper_invs))
    ([], []) pres
  
(** Expand definitions of specvars [todo] in specvars [acc] *)
let rec expand_vardefs acc todo =
  match todo with
  | (v, _ as vdef)::todo' ->
      let s (v, def) = (v, subst [vdef] def) in
      expand_vardefs (List.map s acc) (List.map s todo') 
  | _ -> List.map (fun (v, f) -> (v, unlambda f)) acc

let collect_old_preds vardefs global_env idents ghost_vs_env f =
  (* extract atomic formulae from f *)
  let ghost_vs = List.map fst ghost_vs_env in 
  let skolem_consts, env, atoms0, _ = BohneRefine.extract_preds global_env [] (subst vardefs f) in
  (* remove atoms which do not exlusively speak about initial states *)
  let aux_vars = ghost_vs @ skolem_consts in 
  let atoms = List.filter 
      (fun f -> is_oldform aux_vars f &&
	not (Util.empty (Util.difference (fv f) aux_vars))) atoms0 
  in
  (* generate predicates from atoms *)
  let res = BohneRefine.preds_from_atoms 0 vardefs (ghost_vs @ idents) ghost_vs skolem_consts env atoms in
  res




(** Compute global type environment for program prog and procedure p *)
let get_global_env prog p =
  let class_names = List.map (fun c -> (c, mk_obj_set_type)) (get_class_names prog) in
  let im_vars =
    List.fold_left (fun acc im -> List.fold_left 
	(fun acc d -> (d.vd_name, d.vd_type) :: acc) acc im.im_vars) [] prog.p_impls
  in
  let spec_vars =
    List.fold_left (fun acc spec -> List.fold_left 
	(fun acc d -> (d.vd_name, d.vd_type) :: acc) acc spec.sm_spec_vars) [] prog.p_specs
  in
  let old_spec_vars =
    List.map (fun (v, ty) -> (oldname v, ty)) (union im_vars spec_vars)
  in
  let p_locals = 
    List.fold_left (fun acc d -> (d.vd_name, d.vd_type) :: acc) [] p.p_locals
  in
  let p_formals = List.rev_map (fun d -> (d.vd_name, d.vd_type)) p.p_header.p_formals in
  (all_alloc_objs, mk_obj_set_type) :: union im_vars spec_vars @ 
  old_spec_vars @ p_locals @ p_formals @ class_names

(** Identify conjuncts of the form (EX x. F) in precondition and introduce Skolem constant for x *)
let skolemize_pre_condition m pre_conds =
  let pre_conds', ghost_vs = List.fold_left (fun (pre_conds', ghost_vs) f ->
    match fst (TypeReconstruct.reconstruct_types [] (unlambda (subst m f))) with 
    | Binder (Exists, [(v,ty)], f1) when ty = mk_object_type ->
	let new_v = fresh_name v in
	subst [(v, mk_var new_v)] f1::f::pre_conds', (new_v, ty) :: ghost_vs
    | _ -> f::pre_conds', ghost_vs) ([], []) pre_conds
  in smk_and pre_conds', ghost_vs

(** Identify conjuncts of the form (ALL x. old F --> G) in post condition where x 
   can be replaced by a ghost variable and F moved to pre condition *)
let skolemize_post_condition invs pre_cond post_cond type_sets =
  let find_var_of_type v ty pres new_ghost_vs ghost_vs =
    let pre = smk_and pres in
    let rec find acc = function
      |	[] -> 
	  let v1 = fresh_name v in 
	  ((v1, ty), subst [(v, mk_var v1)] pre) :: new_ghost_vs, v1, ghost_vs
      |	((v1, ty1), pre1) as vtp :: vs -> 
	  if FormUtil.equal_types ty ty1 && 
	    fst (is_unifiable [] [v1] pre1 pre)
	  then new_ghost_vs, v1, List.rev_append acc ghost_vs
	  else find (vtp :: acc) vs
    in find [] ghost_vs
  in
  let posts = split_conjuncts post_cond in
  let pre_cond', post_cond', ghost_vs =
    List.fold_left (fun (pre_cond', post_cond', ghost_vs) -> function
      | App (Const Comment, [_; Binder (Forall, vts, (App (Const Impl, [f1; f2]) as f1_f2))])
      | Binder (Forall, vts, (App (Const Impl, [f1; f2]) as f1_f2)) as f ->
	  let f_in_pre = List.exists (fun f' -> equal f f') pre_cond' in
	  let vs = List.map fst vts in
	  let old_pre_f1, post_f1 = List.partition (is_oldform (vs @ type_sets)) (split_conjuncts f1) in
	  (match old_pre_f1 with
	  | [] -> pre_cond', f::post_cond', ghost_vs
	  | _ ->
	      let pre, post = List.fold_left (fun (pre, post) old_f ->
		let f = remove_old old_f in
		let query = smk_impl (smk_and (invs @ pre_cond'), smk_exists (vts, smk_and (f::pre))) in
		if BfCachedDecider.decide trivial_context query 
		then f::pre, post else pre, old_f::post) ([], []) old_pre_f1 
	      in
	      let new_ghost_vs, vts1, sub, _ = 
		List.fold_left (fun (new_ghost_vs, vts1, sub, ghost_vs) (v, ty) ->
		  let new_ghost_vs', v1, ghost_vs' = find_var_of_type v ty pre new_ghost_vs ghost_vs in
		  (new_ghost_vs', (v1, ty)::vts1, (v, TypedForm (mk_var v1, ty))::sub, ghost_vs')) 
		  ([], [], [], ghost_vs) vts 
	      in
	      (* Heuristic: instantiate f in precondition with chosen ghost variables *)
	      let pre_cond' = 
		if f_in_pre then 
		  let pre_without_f = List.filter (fun f' -> not (equal f f')) pre_cond' in
		  subst sub f1_f2 :: pre_without_f
		else pre_cond' in 
	      List.fold_left (fun acc f -> subst sub f :: acc) pre_cond' pre, 
	      smk_impl (smk_and (List.map (subst sub) (post @ post_f1)), subst sub f2) :: post_cond',
	      List.rev_append new_ghost_vs ghost_vs)
      | f -> pre_cond', f::post_cond', ghost_vs) (pre_cond, [], []) posts
  in pre_cond', post_cond', ghost_vs

(** Compute precondition, postcondition, and background formula *)
let get_pre_and_post prog im spec shorthands vardefs p =
  let post_cond0 = concretized_post prog im p spec p.p_body in
  let post_cond1 = unlambda (subst ((oldname this_id, mk_var this_id):: shorthands) (post_cond0)) in
  let post_cond2, _ = TypeReconstruct.reconstruct_types [] post_cond1 in
  let pre_cond0 = concretized_pre prog im spec in
  let p_formals = List.rev_map (fun d -> (d.vd_name, d.vd_type)) p.p_header.p_formals in
  let background = 
    List.map (fun (v, ty) -> mk_eq (TypedForm (mk_var (oldname v), ty), TypedForm (mk_var v, ty))) p_formals @
    (if !CmdLine.background then 
      mk_eq (TypedForm (mk_var (oldname this_id), mk_object_type), TypedForm (mk_var this_id, mk_object_type)):: 
      (* mk_eq (TypedForm (mk_var this_id, mk_object_type), TypedForm (mk_var (oldname this_id), mk_object_type)):: *)
      Background.get_alloc_conditions prog im (fv pre_cond0)
    else [])
  in
  let pre_cond1, pre_ghost_vars = skolemize_pre_condition (shorthands @ vardefs) (split_conjuncts pre_cond0) in
  let pre_cond2 = unlambda (subst shorthands pre_cond1) in
  let pre_cond3, _ = TypeReconstruct.reconstruct_types [] pre_cond2 in
  let pre_cond4, invs = find_candidate_invariants pre_cond3 in
  let _ =  Debug.lmsg 3 (fun () ->
    "Loop invariant candidates:\n" ^ string_of_form (smk_and invs) ^ "\n") 
  in
  let pre_cond, post_cond, post_ghost_vars = 
    let type_sets = get_class_names prog in
    skolemize_post_condition (background @ invs) pre_cond4 post_cond2 (this_id::type_sets)
  in
  let _ = Debug.lmsg 2 (fun () ->
    "Precondition of procedure:\n" ^ string_of_form (smk_metaand (pre_cond @ background)) ^ 
    "\n\nPost condition of Procedure :\n" ^ string_of_form (mk_metaand post_cond) ^ "\n")
  in
  (* let pre_cond = subst vardefs (smk_and pre_cond3) in *)
  smk_and pre_cond, post_cond, background, invs, pre_ghost_vars, post_ghost_vars


(** Extract predicate candidates from a formula. *)
let get_pred_candidates = 
  let counter = ref 0 in
  let mk_unique_name id =
    counter := !counter + 1;
    Printf.sprintf "%s_%d" id !counter
  in
  fun m f ->
  let merge cls = 
    let merge_candidates cl1 cl2 =
      let add cl (f, vt) =
	if List.mem_assoc f cl then cl
	else (f, vt) :: cl
      in List.fold_left add cl2 cl1
    in
    List.fold_left merge_candidates [] cls 
  in
  let is_candidate f x ty bound m = 
    match ty with
    | TypeApp (TypeSet, [TypeApp (TypeObject, [])]) ->
	Util.empty (Util.intersect (fv f) bound) &&
	(is_oldname x && List.mem_assoc (unoldname x) m ||
	List.mem_assoc x m)
    | _ -> false
  in
  let add_candidate bound m f v ty = 
    if not (is_candidate f v ty bound m) then [] else
    let predname, ty' = match normalize_type ty with
    | TypeFun ([_], ty') ->
	(match unnotate_all_types f with
	| App (_, [Var arg]) -> v ^ "_" ^ arg, ty'
	| _ -> mk_unique_name v, ty')
    | _ -> v, ty
    in 
    [(f, (v, ty', predname))]
  in
  let rec get_candidates (bound:ident list) (f:form) = 
  match f with
  | App (Const Card, [TypedForm (Var _, _) as f'])
  | App (Const Card, [App (TypedForm (Var _, _), _ :: _) as f']) 
  | App (Const Card, [App (Const FieldRead, TypedForm (Var _, _) :: _ :: _) as f']) ->
      get_candidates bound f'
  | App (Const Card, [f0]) ->
      let f1 = unlambda f0 in
      let ty = TypeReconstruct.get_type [] f1 in 
      let old_f1 = make_old_and_transform f1 [] in
      let v = oldname (mk_unique_name "cardpred") in
      add_candidate bound ((v, old_f1) :: m) old_f1 v ty 
  | App (Const FieldRead, TypedForm (Var v, ty) :: f' :: fs)
  | App (TypedForm (Var v, ty), f' :: fs) ->
      let f1 = unlambda (App (TypedForm (Var v , ty), [f'])) in
      let cl = add_candidate bound m f1 v ty in
      merge (cl :: List.rev_map (get_candidates bound) (f' :: fs))
  | App (f1, fs) ->
      merge (List.rev_map (get_candidates bound) (f1 :: fs))
  | Binder (k,tvs,f1) ->
      let add_bound vs (v, t) = v :: vs in
      get_candidates (List.fold_left add_bound bound tvs) f1
  | Var v -> []
  | Const _ -> []
  | TypedForm (Var v, ty) -> 
      add_candidate bound m (Var v) v ty 
  | TypedForm (f1, _) -> get_candidates bound f1
  in get_candidates [] f

(** Collect predicates from pre- and postcondition *)
let collect_preds global_env m vardefs preds =
  let is_object_type = function
    | TypeApp (TypeObject, []) -> true
    | _ -> false
  in
  let rec collect_preds preds = function
    | [] -> preds
    | (f, (x, ty, predname)) :: todo -> 
	(* Printf.printf "%s == %s" x (string_of_form f); *)
	match normalize_type ty with
	| TypeApp (TypeObject, ([] as ts)) 
	| TypeApp (TypeSet, [TypeProd ts])
	| TypeApp (TypeSet, ts) 
	| TypeApp (TypeBool, ([] as ts))  when List.for_all is_object_type ts ->
	    let deps, shorthands =
	      let vars_in_def =
		try
		  let f_expanded =
		    let def = 
		      if is_oldname x then 
			make_old_and_transform (List.assoc (unoldname x) m) [] 
		      else List.assoc x m
		    in
		    unlambda (subst [(x, def)] f)
		  in
		  get_pred_candidates m f_expanded
		with Not_found -> []
	      in
	      let deps, sh_names =
		List.partition (function 
		  | (_, (_, TypeApp (TypeBool, []), _))
		  | (_, (_, TypeApp (TypeObject, []), _))
		  | (_, (_, TypeApp (TypeSet, [TypeApp (TypeObject, [])]), _)) -> true
		  | _ -> false) vars_in_def
	      in
	      deps, List.map (fun (_, (v, _, _)) -> 
		(v, 
		 if is_oldname v then
		   make_old_and_transform (List.assoc (unoldname v) vardefs) [] 
		 else List.assoc v vardefs)) sh_names
	    in
	    let f', todo' = 
	      if is_oldname x then
		let todo' =
		  try ignore (BohnePred.search (unoldname x)); todo
		  with Not_found -> (remove_old (transform_old f), (unoldname x, ty, unoldname predname)) :: todo
		in
		f, deps @ todo'
	      else
		let sub = 
		  try [(x, subst shorthands (List.assoc x m))]
		  with Not_found -> []
		in
		unlambda (subst sub f), 
		deps @ todo
	    in
	    let def = match ts with
	    | [] -> f'
	    | _ -> 
		let arity = List.length ts in
		let typed_vars = typed_free_var_list arity in
		let vars = List.map (fun (x, ty) -> TypedForm (mk_var x, ty)) typed_vars in
		let elem = match vars with [x] -> x | _ -> mk_tuple vars in
  		Binder (Comprehension, typed_vars, mk_elem (elem, f'))
	    in
	    let props = 
	      (if is_oldname x then [IsConst; IsOld (unoldname predname)]
	      else []) @
	      (match deps with
	      | [] -> []
	      | _ -> [DependsOn (List.map (fun (_, (_, _, pname)) -> pname) deps)])		   
	    in
	    let x_pred = 
	      try get_pred_by_def def 
	      with
	      |	Not_found -> add_pred_decl predname def props 
	    in
	    collect_preds (union_preds [x_pred] preds) todo'
	| _ -> collect_preds preds todo
  in collect_preds preds

(** Desugar procedure into a Bohne program *)
let convert_proc prog im spec m0 p =
  (* initialize Bohne program *)
  let shorthands = 
    let sh_names = filter_map (fun v -> v.vd_abstract) (fun v -> v.vd_name) im.im_vars in
    List.filter (fun (v, def) -> List.mem v sh_names) im.im_vardefs 
  in
  let m = Util.union p.p_vardefs (Util.union m0 im.im_vardefs) in
  let m = List.map 
      (function 
	| (v, App(Const Old, [Var x])) -> (v, Var (oldname x))
	| (v, App(Const Old, [TypedForm(Var x, ty)])) -> (v, TypedForm (Var (oldname x), ty))
	| v_def -> v_def)
      m
  in
  let vardefs = expand_vardefs m m in
  let exit_point = fresh_program_point () in
  let entry_point = find_program_point exit_point p.p_body in
  let global_env = get_global_env prog p in
  let wp cs f = 
    let wp_bc = wp_bc prog im p spec vardefs None in
    let wp_f = List.fold_left (fun f c -> wp_bc c f) f cs in
    (* alpha_rename (Util.union idents (fv f)) *) wp_f
  in
  let pre_cond, post_cond, background, invs, pre_ghost_vars, post_ghost_vars =
    get_pre_and_post prog im spec shorthands vardefs p
  in
  let global_env = 
    global_env @
    List.map (fun (x, env) -> (oldname x, env)) global_env @
    pre_ghost_vars @ 
    List.map fst post_ghost_vars
  in
  let idents = List.map fst global_env @ pseudo_constants in 
  let program = 
    {program_name = im.im_name ^ "." ^ p.p_header.p_name;
     locations = Hashtbl.create 0;
     entry_point = entry_point;
     exit_point = exit_point;
     wp = wp;
     vardefs = vardefs;
     assumed_invariants = invs;
     background = (List.map (mk_comment "background") background);
     initial_states = pre_cond;
     global_env = global_env;
     idents = idents;
     post_ghost_vars = post_ghost_vars}
  in
  let remove_type_annot af = 
    let class_names = get_class_names prog in
    let is_not_type_annot = function
      |	(App (Const Elem, [_; TypedForm (Var v, _)]))
      |	(App (Const Elem, [_; Var v])) ->
	  not (List.mem v class_names)
      |	_ -> true
    in
    let type_annot = Str.regexp ".*type$" in
      if Str.string_match type_annot af.annot_msg 0 then 
      {af with annot_form = mk_true} else 
    let fs = match af.annot_form with
    | App (Const And, fs)
    | App (Const MetaAnd, fs) -> fs
    | f -> [f]
    in {af with annot_form = smk_and (List.filter is_not_type_annot fs)}    
  in
  (* collect some predicates *)
  let final_preds0 = 
    collect_preds global_env m vardefs [] (get_pred_candidates m (annotate_types program.global_env (smk_and post_cond))) 
  in
  let initial_preds0 =
    collect_preds global_env m vardefs (null_decl::final_preds0) (get_pred_candidates m pre_cond)
  in
  let mk_initial_preds pp = 
    List.map (fun p -> add_pred p.pred_def (Inherit [pp]::p.pred_props)) initial_preds0 
  in
  let mk_old_preds = 
    let old_preds = collect_old_preds vardefs program.global_env program.idents (List.map fst post_ghost_vars) (smk_and post_cond)
    in
    fun pp ->  List.map (fun p -> add_pred p.pred_def (Inherit [pp]::p.pred_props)) old_preds
  in      
  let final_preds = union_preds (mk_old_preds exit_point) final_preds0 in
  let initial_preds = ref (union_preds (mk_old_preds entry_point) initial_preds0) in
  let ghost_preds pp = List.map (add_var_pred_decl pp) pre_ghost_vars in     
  (* convert AST into CFG of guarded commands *)
  let add_location exit (preds, seqs) asserts =
    let mk_gc havoc guard seq = {gc_havoc = havoc; gc_guard = guard; gc_command = seq} in
    let process_seq (entry, havoc, seq) =
      let loc = 
	try Hashtbl.find program.locations entry.pp_id 
	with Not_found ->
	  let new_loc = 
	    {loc_pp = entry;
	     loc_cmds = [];
	     loc_preds = union_preds (union_preds (mk_initial_preds entry) (ghost_preds entry)) (mk_old_preds entry);
	     loc_split_preds = [];
	     loc_invariants = List.map (mk_comment background_marker) background (* invs *);
	     loc_assertions = List.map (fun a -> (gc_skip (), a)) asserts}
	  in Hashtbl.add program.locations entry.pp_id new_loc; new_loc
      in 
      loc.loc_preds <- union_preds loc.loc_preds preds;
      if not (empty seq && empty havoc) then 
	loc.loc_cmds <- (mk_gc havoc mk_true seq, exit) :: loc.loc_cmds
    in
    List.iter process_seq seqs
  in
  let is_havoc_effected hfs = 
    let havoc_vs = List.concat (List.map fv hfs) in
    fun (c : basic_command) ->
      let c_vs = match c with
      |	Skip -> []
      |	Assert af -> fv af.hannot_form
      |	Assume af -> fv af.annot_form
      |	VarAssign va ->
	  va.assign_lhs :: fv va.assign_rhs
      |	_ -> failwith "found basic command in BohneInterface.is_havoc_effected that should have been desugared."
      in 
      not (Util.disjoint havoc_vs c_vs)
  in
  let add_cmd (preds, seqs) c0 = 
    let expand af =
      {annot_form = subst shorthands af.annot_form; 
       annot_about = None;
       annot_msg = af.annot_msg}
    in
    let hexpand af =
      {hannot_form = subst shorthands af.hannot_form; 
       hannot_about = None;
       hannot_msg = af.hannot_msg;
       hannot_hints = [];
       hannot_forSuch=[];
      }
    in
    let c = match c0 with
    | Assume af -> Assume (expand af)
    | Assert af -> Assert (hexpand af)
    | NoteThat af -> NoteThat (hexpand af)
    | Split af -> Split (expand af)
    | _ -> c0
    in
    let get_primed_preds ff = 
      (
       let collected = collect_preds global_env m vardefs [] (get_pred_candidates m ff) in
       let init_preds, preds' = List.fold_left (fun (init_preds, preds') p ->
	if is_old p then
	  let new_p = pred_by_name (find_map (function IsOld p -> Some p | _ -> None) p.pred_props) in 
	  (union_preds [p; new_p] init_preds, preds')
	else init_preds, union_preds [p] preds') ([], preds) collected
      in 
      initial_preds := union_preds init_preds !initial_preds;
      preds') 
    in  
    let preds' = match c0 with
    | Assume af | Split af -> get_primed_preds af.annot_form
    | Assert af | NoteThat af -> get_primed_preds af.hannot_form
    | _ -> preds
    in
    (preds', List.rev_map (fun (entry, havocs, seq) -> (entry, havocs, c::seq)) seqs)
  in
  let add_pred (preds, seqs) specvar = 
    let def = 
      try List.assoc specvar vardefs
      with Not_found -> 
	Util.warn ("Tracked unknown specvar '" ^ specvar ^ "'"); 
	mk_true 
    in
    let preds' = 
      let ty = TypeReconstruct.get_type global_env def in
      collect_preds global_env m vardefs preds [(def, (specvar, ty, specvar))]
    in 
    (preds', seqs)
  in    
  let mk_annot_form fs = {annot_form = smk_and fs; annot_about = None; annot_msg = ""} in
  let mk_hannot_form fs = {hannot_form = smk_and fs; hannot_about = None; 
			   hannot_msg = ""; hannot_hints=[]; hannot_forSuch=[]} in
  let append_seqs (preds1, seqs1) (preds2, seqs2) =
    (union_preds preds1 preds2, List.rev_append seqs1 seqs2)
  in
  let _ = add_location exit_point (final_preds, [(exit_point, [], [])]) post_cond in
  let orig_post_cond = concretized_post prog im p spec p.p_body in
  let rec convert_command seqs cs =
	match cs with
	| c::cs' -> (match c with
	  | Basic bc -> 
	      (match bc.bcell_cmd with
	      |	Hint (TrackSpecvar tsv) ->
		  convert_command (add_pred seqs tsv.track_var) cs'
              (* treat "assume false" as a return statement *)
	      |	Assume afc when afc.annot_form = mk_false ->
		  add_location exit_point seqs []; ([], []) 
	      | Assume afc when not !CmdLine.background ->
		  convert_command (add_cmd seqs (Assume (remove_type_annot afc))) cs'
	      (* replace old post condition with skolemized one *)
	      |	Assert afc when equal afc.hannot_form orig_post_cond ->
		  let annot_post = mk_hannot_form post_cond in
		  convert_command (add_cmd seqs (Assert annot_post)) cs'
	      |	Havoc h ->
		  let havocs = List.map (fun f ->
		    annotate_types global_env f) h.havoc_regions
		  in
		  (match seqs with 
		  | (preds, [(havoc_point, ((_ :: _) as havocs'), [])]) ->
		      convert_command (preds, [(havoc_point, havocs' @ havocs, [])]) cs'
		  | (preds, sq) ->
		      (* let havoc_pre_point = fresh_program_point ()
                        (* find_program_point exit_point c *) in
			let havoc_post_point = fresh_program_point () in
			let _ = add_location havoc_pre_point seqs [] in
			let _ = add_location havoc_post_point ([], [(havoc_pre_point, havocs, [])]) [] in
			convert_command ([], [(havoc_post_point, [], [])]) cs') *)
		      if List.for_all (fun (_, _, cs) -> List.for_all (fun c -> not (is_havoc_effected havocs c)) cs) sq
		      then 
			let sq' = List.map (fun (pp, havocs', cs) -> (pp, havocs' @ havocs, cs)) sq in
			convert_command (preds, sq') cs'
		      else
			let havoc_point = fresh_program_point ()			
                        (* find_program_point exit_point c *) in
			let _ = add_location havoc_point seqs [] in
			convert_command ([], [(havoc_point, havocs, [])]) cs')
	      |	ProcCall _ -> failwith "Bohne: procedure call should have been desugared: use option -sastvc."
	      |	Alloc _ -> failwith "Bohne: new statement should have been desugared: use option -sastvc."
	      |	cmd -> 
		  (* match seqs with
		  | (preds, [(_, _ :: _, [])]) ->
		      let p_point = fresh_program_point () in
		      let _ = add_location p_point seqs [] in
		      convert_command ([], [(p_point, [], [])]) cs 
		  | _ -> *)
		      convert_command (add_cmd seqs cmd) cs') 
	  | Seq cs -> convert_command seqs (cs @ cs')
	  | Choice cs -> 
	      let seqs' = List.fold_left (fun acc c -> 
		append_seqs (convert_command seqs [c]) acc) ([], []) cs 
	      in convert_command seqs' cs'
	  | If ic -> 
	      let it_cond = Assume (mk_annot_form [ic.if_condition])
	      and ie_cond = Assume (mk_annot_form [smk_not ic.if_condition]) in
	      let seqs_it = convert_command (add_cmd seqs it_cond) [ic.if_then]
	      and seqs_ie = convert_command (add_cmd seqs ie_cond) [ic.if_else] in
	      convert_command (append_seqs seqs_it seqs_ie) cs'
	  | Assuming ac ->
	      convert_command seqs (ac.assuming_body @ cs')
	  | PickAny pc ->
	      convert_command seqs (pc.pa_body @ cs')
	  | PickWitness pw ->
	      convert_command seqs (pw.pw_body @ cs')
	  | Induct ic ->
	      convert_command seqs (ic.induct_body @ cs')
	  | Contradict cc ->
	      convert_command seqs (cc.contradict_body @ cs')
	  | Proof pc ->
	      convert_command seqs (pc.proof_body @ cs')
	  | Loop lc ->
	      let loop_point = find_program_point exit_point c in
	      let _ = add_location loop_point seqs [] in
	      let loop_inv = 
		try NoteThat (mk_hannot_form [unsome lc.loop_inv])
		with _ -> Skip		  
	      in
	      let assume_enter = Assume (mk_annot_form [lc.loop_test]) in
	      let assume_exit = Assume (mk_annot_form [smk_not lc.loop_test]) in
	      let loop_preseqs = 
		let seqs = convert_command ([], [(loop_point, [], [])]) [lc.loop_prebody] in
		add_cmd seqs loop_inv
	      in
	      let loop_bodyseqs = 
		convert_command (add_cmd loop_preseqs assume_enter) [lc.loop_postbody] 
	      in
	      let _ = add_location loop_point loop_bodyseqs [] in
	      convert_command (add_cmd loop_preseqs assume_exit) cs'
	  | Return rc ->
	      let seqs' =
		match rc.return_exp with
		| None -> seqs
		| Some e -> 
		    let return_c = VarAssign 
			{assign_lhs = result_var; 
			 assign_tlhs = (result_var, spec.p_restype); 
			 assign_rhs = e}
		    in add_cmd seqs return_c
	      in add_location exit_point seqs' []; ([], []))
	  | [] -> seqs
  in 
  let _ = match convert_command (!initial_preds, [(entry_point, [], [])]) [p.p_body] with
  | (_, []) -> ()
  | seqs -> add_location exit_point seqs []
  in 
  let entry_loc = initial_location program in
  entry_loc.loc_preds <- union_preds !initial_preds entry_loc.loc_preds;
  program

(** Initialize all modules *)
let init () =
  BohneOptions.readCmdLine ();
  BfCachedDecider.reset_stats ();
  BfCachedDecider.clear_cache ();
  BohnePred.reset ()
  

open Bf
open Bf_set

(** Annotate procedure with result of analysis *)
let annotate_proc ast_prog program lfp root_region p =
  let mk_assume f msg =
    let mk_basic_cell c = Basic
	{bcell_cmd = c;
	   bcell_point = fresh_program_point ();
	 bcell_known_before = [];
	 bcell_known_after = []}
    in
    if f = mk_true then [] else
    [mk_basic_cell (Assume {annot_form = f; annot_about = None;annot_msg = msg})]
  in
  let mk_decaf_inv pp = 
    let loc = get_location program pp in
    let inv = smk_and loc.loc_invariants (* smk_and (collect_invariants root_region pp) *) in
    let _ = Debug.print_msg 1 (fun chan -> 
      Printf.fprintf chan "Annotating invariant for location %d:\n" pp.pp_id;
      output_string chan (string_of_form (strip_types inv) ^ "\n"))
    in inv
  in
  let mk_bohne_inv pp =
    let loc = get_location program pp in
    let preds = loc.loc_preds in
    let abs_state_list, lfp_preds = project_lfp lfp pp.pp_id in
    let inv_preds = if is_exit_pp program pp then null_decl::preds else lfp_preds in
    let abs_inv = List.fold_left (fun acc (_, s) -> Bf.disj s acc) Bf.bottom abs_state_list in
    let state_inv = concretize_state_invariant inv_preds abs_inv in
    let old_invs = 
      let sub = List.map (fun p -> (p.pred_name, p.pred_def)) lfp_preds in
      let old_invs0 = concretize_old_invariant lfp_preds abs_inv in
      List.map (fun f0 ->
	let f = subst sub f0 in
	let fv_f = fv f in
	let ghost_vs_f = List.filter (fun ((v, _), _) -> List.mem v fv_f) program.post_ghost_vars in
	let gvs, pres = List.split ghost_vs_f in 
	smk_foralls (gvs, smk_impl (oldify true (List.map fst gvs @ get_class_names ast_prog) (smk_and pres), f))) old_invs0
    in
    let abs_region_invs = collect root_region pp in
    let _ = Debug.print_msg 1 (fun chan -> 
      Printf.fprintf chan "Annotating invariant for location %d:\n" pp.pp_id;
      print_abs_states chan 
	(List.fold_left 
	   (fun acc s -> Bf_set.union acc s) Bf_set.bottom abs_region_invs))
    in    
    let region_invs = smk_or (List.rev_map (fun abs_states -> 
      (* gamma_state false inv_preds (Bf_set.join abs_states) *)
	gamma false inv_preds abs_states) abs_region_invs)
    in
    smk_and (state_inv :: region_invs :: old_invs)
  in
  let final_assumes = 
    if !CmdLine.bohne_abstract_final then 
      mk_assume (mk_bohne_inv program.exit_point) "Bohne decaf claims" @
      mk_assume (mk_decaf_inv program.exit_point) "Bohne claims"
    else []
  in
  let rec write_back has_succs c =
    match c with 
    | Basic bc -> 
	(match bc.bcell_cmd with
	 (* treat "assume false" as a return statement *)
	| Assume afc when afc.annot_form = mk_false ->
	    false, c
	| Assert afc when not has_succs ->
	    true, Seq (final_assumes @ [c])
	| _ -> true, c)
    | Return _ -> false, Seq (final_assumes @ [c])
    | Seq cs -> 
	let has_succs', cs' = 
	  List.fold_right 
	    (fun c (has_succs, cs') ->
	      let has_succs', c' = write_back has_succs c in 
	      has_succs', c' :: cs') 
	    cs (has_succs, [])
	in has_succs', Seq cs'
    | Choice cs -> 
	let has_succs', cs' = 
	  List.fold_right 
	    (fun c (has_succs', cs') ->
	      let c_has_succs, c' = write_back has_succs c in
	      has_succs' || c_has_succs, c' :: cs')
	    cs (false, [])
	in
	has_succs', Choice cs'
    | If ic -> 
	let _, it' = write_back has_succs ic.if_then in
	let _, ie' = write_back has_succs ic.if_else in
	let ic' = {ic with if_condition = ic.if_condition;
		     if_then = it';
		     if_else = ie'}
	in true, If ic'
    | PickAny pc ->
	let has_succs', pa_body' = 
	  List.fold_right 
	    (fun c (has_succs, cs') ->
	      let has_succs', c' = write_back has_succs c in 
	      has_succs', c' :: cs') 
	    pc.pa_body (has_succs, [])
	in has_succs', PickAny {pc with pa_body = pa_body'}
    | PickWitness pw ->
	let has_succs', pw_body' = 
	  List.fold_right 
	    (fun c (has_succs, cs') ->
	      let has_succs', c' = write_back has_succs c in 
	      has_succs', c' :: cs') 
	    pw.pw_body (has_succs, [])
	in has_succs', PickWitness {pw with pw_body = pw_body'}
    | Assuming ac ->
	let has_succs', assuming_body' = 
	  List.fold_right 
	    (fun c (has_succs, cs') ->
	      let has_succs', c' = write_back has_succs c in 
	      has_succs', c' :: cs') 
	    ac.assuming_body (has_succs, [])
	in has_succs', Assuming {ac with assuming_body = assuming_body'}
    | Induct ic ->
	let has_succs', induct_body' = 
	  List.fold_right 
	    (fun c (has_succs, cs') ->
	      let has_succs', c' = write_back has_succs c in 
	      has_succs', c' :: cs') 
	    ic.induct_body (has_succs, [])
	in has_succs', Induct {ic with induct_body = induct_body'}
    | Contradict cc ->
	let has_succs', contradict_body' = 
	  List.fold_right 
	    (fun c (has_succs, cs') ->
	      let has_succs', c' = write_back has_succs c in 
	      has_succs', c' :: cs') 
	    cc.contradict_body (has_succs, [])
	in has_succs', Contradict {cc with contradict_body = contradict_body'}
    | Proof pc ->
	let has_succs', proof_body' = 
	  List.fold_right 
	    (fun c (has_succs, cs') ->
	      let has_succs', c' = write_back has_succs c in 
	      has_succs', c' :: cs') 
	    pc.proof_body (has_succs, [])
	in has_succs', Proof {pc with proof_body = proof_body'}
    | Loop lc -> 
	let pp = find_program_point program.exit_point c in
	let decaf_assumes = mk_assume (mk_decaf_inv pp) "Bohne decaf claims" in
	let loop_assumes = mk_assume (mk_bohne_inv pp) "Bohne claims" in
	let loop_inv' = smk_and (safe_unsome mk_true lc.loop_inv::program.assumed_invariants) in 
	let _, loop_prebody' =  write_back true lc.loop_prebody in
	let _, loop_postbody' =  write_back true lc.loop_postbody in
	let lc' = {lc with loop_inv = Some loop_inv';
		     loop_prebody = Seq (decaf_assumes @ loop_assumes @ [loop_prebody']);
		     loop_test = lc.loop_test;
		     loop_postbody = loop_postbody'}
	in true, Loop lc'
  in 
  if empty root_region.succs then p else
  let _, p_body' = write_back false p.p_body in
  {p_header = p.p_header;
   p_locals = p.p_locals;
   p_vardefs = p.p_vardefs;
   p_body = Seq (p_body'::final_assumes);
   p_simple_body = p.p_simple_body}

(** Main procedure *)
let analyze_proc (prog : program) (im : impl_module)
    (p : proc_def) (spec : proc_header) (m : specvar_def list) : proc_def =
  (* initialize all modules *)
  let _ = init () in
  let _ = 
    if !CmdLine.cache_file_name <> "" then 
      phase "Loading persistent cache" PersistentCache.load_cache ()
  in
  (* convert proc p into a Bohne program *)
  let program = convert_proc prog im spec m p in
  (* let _ = eliminate_havocs program in *)
  let _ = propagate_asserts_assumes program in
  let _ = 
    if !BohneOptions.opt_derive_preds then
      phase "Deriving initial predicates" derive_initial_predicates program 
  in 
  let _ = 
    if !BohneOptions.opt_propagate_preconditions then
      phase "Propagating context" BohneDecaf.analyze program 
  in
  let _ = Debug.print_msg 1 (fun chan -> print_program chan program) in
  (* exit 1; *)
  (* analyze Bohne program *)
  let lfp, root_region = Bohne.analyze program in
  let res = annotate_proc prog program lfp root_region p in
  let _ = if !CmdLine.storecache then
    phase "Storing persistent cache" BfCachedDecider.store_persistent_cache ()
  in
  (* print_endline (PrintAst.pr_proc_def "" res); *)
  res
