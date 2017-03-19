(* Translates Form to the subset of Form supported by SMT-LIB *)

open Form
open FormUtil
open TypeReconstruct
open TermRewrite
open Common

let cvcl_rewrite_ite = ref true
  (* if setting to false, make sure that you are never relying on polarity
     of ite arguments, because they do not have a well-defined polarity *)

(* This is a shorthand for printing debug messages for this module. *)
let debug_id : int = Debug.register_debug_module "SmtTranslate"
let debug_msg : (string -> unit) = Debug.debug_msg debug_id
let debug_is_on () : bool = Debug.debug_is_on debug_id

let not_yet_declared (env : typeEnv) (i : ident) : bool =
  (not (List.exists (fun (id, _) -> id = i) env))

let get_type (env : typeEnv) (i : ident) : typeForm =
  try
    let _, ty = List.find (fun (id, _) -> id = i) env in ty
  with Not_found -> failwith ("get_type could not find type for " ^ i ^ "\n")

let declare (env : typeEnv) (i : ident) (ty : typeForm) : typeEnv =
  if (not_yet_declared env i) then
    (debug_msg ("declare: " ^ i ^ " : " ^ (PrintForm.string_of_type ty) ^ "\n");
     (i, ty) :: env)
  else env

let remove_declaration (env : typeEnv) (i : ident) : typeEnv =
  List.filter (fun (x, _) -> (x <> i)) env

let globalArrayObjectType = (TypeApp (TypeDefined "globalArrayObj", []))

let declare_arrayRead (env : typeEnv) (ty : typeForm) : typeEnv =
  let id = "arrayRead" in
    declare env id 
      (FormUtil.mk_fun_type 
	 [globalArrayObjectType; FormUtil.mk_object_type; FormUtil.mk_int_type]
	 ty)

let declare_arrayWrite (env : typeEnv) (ty : typeForm) : typeEnv =
  let id = "arrayWrite" in
    declare env id
      (FormUtil.mk_fun_type [globalArrayObjectType; FormUtil.mk_object_type; 
			     FormUtil.mk_int_type; ty] 
	 globalArrayObjectType)

let get_elem_type (env : typeEnv) (id : ident) : typeForm =
  let ty = get_type env id in
    match ty with
      | TypeApp(TypeArray, [_; TypeFun([TypeApp(TypeInt,[])], ty')])
      | TypeApp(TypeArray, [_; TypeApp(TypeArray,[_; ty'])]) 
      | TypeFun(_, TypeApp(TypeArray,[_; ty']))
      | TypeFun(_, TypeFun([TypeApp(TypeInt,[])], ty')) -> ty'
      | _ -> debug_msg 
	  ("get_elem_type: " ^ (MlPrintForm.string_of_type ty) ^ "\n");
	  raise Not_found

(* Add any necessary declarations, and returns the new state. *)
let rec process_formula (env : typeEnv) (f : form) : typeEnv =
  match f with
    | (Const NullConst) ->
	(* Declare null if necessary. *)
	let f0 = Form.string_of_const NullConst in 
	  declare env f0 FormUtil.mk_object_type
    | App(Const ArrayRead, (Var v :: frest)) ->
	let env =
	  try
	    let ty = get_elem_type env v in
	    let env = remove_declaration env "arrayRead" in
	      declare_arrayRead env ty
	  with Not_found -> env in
	let env = remove_declaration env v in
	let env = declare env v globalArrayObjectType in
	  List.fold_left process_formula env frest
    | App(Const ArrayRead, fs) ->
	let env = declare_arrayRead env FormUtil.mk_object_type in
	  List.fold_left process_formula env fs
    | App(Const ArrayWrite, (Var v :: frest)) ->
	let env =
	  try
	    let ty = get_elem_type env v in
	    let env = remove_declaration env "arrayWrite" in
	      declare_arrayWrite env ty
	  with Not_found -> env in
	let env = remove_declaration env v in
	let env = declare env v globalArrayObjectType in
	  List.fold_left process_formula env frest
    | App(Const ArrayWrite, fs) ->
	let env = declare_arrayWrite env FormUtil.mk_object_type in
	  List.fold_left process_formula env fs
    | App(fa, fl) -> 
	List.fold_left process_formula (process_formula env fa) fl
    | Binder(_, _, fb) -> process_formula env fb
    | TypedForm(ft, _) -> 
	    (* There shouldn't be any typed formulas at this point. *)
	failwith ("process_formula: can't handle " ^ (PrintForm.string_of_form f))
    | _ -> env

let process_assumptions (env: typeEnv) (fs : form list) : typeEnv =
  List.fold_left process_formula env fs

(* Eliminate lambda expressions. Applies beta-reduction and other
   transformations. *)
let rec rewriteLambdas (f : form) : form =
  match f with
    | App(Const Eq, [f1; Binder(Lambda, til, f2)])
    | App(Const Eq, [Binder(Lambda, til, f2); f1]) ->
	let til0 = 
	  List.map (fun (id, t) -> (("?" ^ (Util.fresh_name id)), t)) til in
	let newVars = List.map (fun (id, t) -> mk_var id) til0 in
	let oldIds = fst (List.split til) in
	let sm = List.combine oldIds newVars in
	let f' = mk_eq (App(f1, newVars), (subst sm f2)) in
	  Binder(Forall, til0, rewriteLambdas f')
    | App(Binder(Lambda, (id, t) :: til, f0), f1 :: fs) ->
	(* Performs beta-reduction one argument at a time. *)
	let f0' = subst [(id, f1)] f0 in
	  if til = [] then
	    rewriteLambdas (App(f0', fs))
	  else if fs = [] then
	    Binder(Lambda, til, (rewriteLambdas f0'))
	  else
	    rewriteLambdas (App(Binder(Lambda, til, f0'), fs))
    | App(f0, fs) ->
	let f0' = rewriteLambdas f0 in
	let fs' = List.map rewriteLambdas fs in
	  App(f0', fs')
    | Binder(b, til, f0) ->
	Binder(b, til, rewriteLambdas f0)
    | TypedForm(f0, tf) ->
	TypedForm((rewriteLambdas f0), tf)
    | _ -> f

(* Renames variables bound in universal and existential quantifiers
   according to SMTLIB standard. *)
let rec renameBoundVariables (f : form) : form =
  match f with
    | App(f0, fs) ->
	let f0' = renameBoundVariables f0 in
	let fs' = List.map renameBoundVariables fs in
	  App(f0', fs')
    | Binder(Forall as b, til, f0)
    | Binder(Exists as b, til, f0) ->
	(* Prepend "?" to names of quantified variables. *)
	let til0 = List.map (fun (v, t) -> (("?" ^ v), t)) til in
	let oIds = fst (List.split til) in
	let nVars = List.map (fun (v, _) -> mk_var v) til0 in
	let sm = List.combine oIds nVars in
	  Binder(b, til0, renameBoundVariables (subst sm f0))
    | Binder(b, til, f0) ->
	Binder(b, til, renameBoundVariables f0)
    | TypedForm(f0, tf) ->
	TypedForm(renameBoundVariables f0, tf)
    | _ -> f

(* Rewrites field reads and writes as well as array reads and writes
   into Ite, which is then taken care of by another pass. *)
let rec rewriteIntoIte (f : form) : form =
  match f with
    | App(Const FieldRead, [App(Const FieldWrite, [f0; f1; f2]); f3])
    | App(App(Const FieldWrite, [f0; f1; f2]), [f3])
    | App(Const FieldWrite, [f0; f1; f2; f3]) ->
	rewriteIntoIte
	  (FormUtil.mk_ite
	     (FormUtil.mk_eq (f1, f3), f2, (FormUtil.mk_fieldRead f0 f3)))
    | App(App(Const ArrayWrite, [aS; arr0; ind0; val0]), [arr1; ind1])
    | App(Const ArrayRead, 
	  [App(Const ArrayWrite, [aS; arr0; ind0; val0]); arr1; ind1]) ->
	if (arr0 = arr1 & ind0 = ind1) then
	  rewriteIntoIte val0
	else
	  rewriteIntoIte
	    (mk_ite
	       (mk_and [mk_eq (arr0, arr1); mk_eq (ind0, ind1)], val0,
		(mk_arrayRead aS arr1 ind1)))
    | App(Const Ite, [App(Const Eq, [f0; f1]); f2; f3]) ->
	let f0' = rewriteIntoIte f0 in
	let f1' = rewriteIntoIte f1 in
	let f2' = rewriteIntoIte f2 in
	  if (f0' = f1') then f2'
	  else
	    let f3' = rewriteIntoIte f3 in
	      App(Const Ite,[App(Const Eq, [f0'; f1']); f2'; f3'])
    | App(Const Ite, [(Const (BoolConst true)); f0; _])
    | App(Const Ite, [(Const (BoolConst false)); _; f0]) ->
	rewriteIntoIte f0
    | App(f0, fs) ->
	let f0' = rewriteIntoIte f0 in
	let fs' = List.map rewriteIntoIte fs in
	  App(f0', fs')
    | Binder(b, til, f0) ->
	Binder(b, til, rewriteIntoIte f0)
    | TypedForm(f0, tf) ->
	TypedForm(rewriteIntoIte f0, tf)
    | _ -> f

let smt_form (f : form) (defs : form list) : form * form list =
  let transform (f : form) : form =
    renameBoundVariables (rewriteIntoIte (rewriteLambdas f)) in
  let f0 = transform f in
  let defs0 = List.map transform defs in
    (f0, defs0)

(* Renames bound variables so that variable names are unique. *)
let rec unique_variables (f : form) (used : ident list) : (form * ident list) =
  match f with
    | Binder (b, [(i,t)], f0) ->
	if (List.exists (fun(x) -> x = i) used) then
	  let ni = (Util.fresh_name i) in
	  let renamed = subst [(i, (Var ni))] f0 in
	  let (f1, nused) = unique_variables renamed used in
	    (Binder(b, [(ni, t)], f1), nused)
	else
	  let (f1, nused) = unique_variables f0 (i :: used) in
	    (Binder(b, [(i, t)], f1), nused)
    | Binder (b, (i,t) :: til, f0) ->
	if (List.exists (fun(x) -> x = i) used) then
	  let ni = (Util.fresh_name i) in
	  let renamed = subst [(i, (Var ni))] (Binder(b, til, f0)) in
	  let (f1, nused) = unique_variables renamed used in
	    (Binder(b, [(ni, t)], f1), nused)
	else
	  let (f1, nused) = unique_variables (Binder(b, til, f0)) (i :: used) in
	    (Binder(b, [(i, t)], f1), nused)
    | App (f0, fs) ->
	let (f1, used0) = unique_variables f0 used in
	let (fs1, used1) = unique_variables_list fs used0 in
	  (App(f1, fs1), used1)
    | TypedForm (_,_) ->
	failwith ("unique_variables: Can't handle " ^ (PrintForm.string_of_form f))
    | _ -> (f, used)
and unique_variables_list 
    (fs : form list) (used : ident list) : (form list * ident list) =
  match fs with
    | [] -> (fs, used)
    | f0 :: fs0 ->
	let (f1, used0) = unique_variables f0 used in
	let (fs1, used1) = unique_variables_list fs0 used0 in
	  ((f1 :: fs1), used1)

(* Returns the skolemized formula and a list of the new skolem functions. *)
  (* !!! should til be threaded or not? currently it's inconsistent *)
let rec skolemize (f : form) (til : typedIdent list) : (form * typedIdent list) =
  match f with
    | Binder (Forall, til0, f0) ->
	let (f1, til1) = skolemize f0 (til @ til0) in
	  (Binder(Forall, til0, f1), til1)
    | Binder (Exists, til0, App (Var trigger, f0 :: _)) when is_trigger trigger -> 
	skolemize (Binder (Exists, til0, f0)) til
    | Binder (Exists, til0, f0) ->
	let (il, tl) = List.split til0 in
	let il0 = List.map 
	  (fun (x) -> 
	     (Util.fresh_name
		((String.uncapitalize 
		    (String.sub x 1 ((String.length x) - 1))) ^ "Sk"))) il in
	let (args, argts) = List.split til in
	let tl0 = List.map 
	  (fun (x) -> if (argts = []) then x else (FormUtil.mk_fun_type argts x)) tl in
	let til1 = List.combine il0 tl0 in
	let argvs = List.map (fun (x) -> (Var x)) args in
	let nil = List.map 
	  (fun (x) -> if (argvs = []) then (Var x) else App ((Var x), argvs)) il0 in
	let rename_map = List.combine il nil in
	let (f1, til2) = skolemize (subst rename_map f0) til in
	  (f1, til1 @ til2)
    | App(Const Ite, [f1;f2;f3]) ->
	if is_binder_free f1 then
	  (let (f1p, til1) = skolemize f1 til in
	   let (f2p, til2) = skolemize f2 til1 in
	   let (f3p, til3) = skolemize f3 til2 in
	     (App(Const Ite, [f1p;f2p;f3p]), til3))
	else 
	  (Util.warn("ite has a quantified argument, turn on cvcl_rewrite_ite");
	   f, til)
    | App (f0, fs) ->
	let (f1, til1) = skolemize f0 til in
	let (fs1, til2) = skolemize_list fs til in
	  (App (f1, fs1), til1 @ til2)
    | TypedForm (f1,t) -> 
	let (f1p, til1) = skolemize f1 til in
	  (TypedForm(f1p, t), til1)
    | _ -> (f, [])
and skolemize_list 
    (fs : form list) (til : typedIdent list) : (form list * typedIdent list) = 
  match fs with
    | [] -> (fs, [])
    | f0 :: fs0 ->
	let (f1, til1) = skolemize f0 til in
	let (fs1, til2) = skolemize_list fs0 til in
	  ((f1 :: fs1), til1 @ til2)

(* fs0 is the to-be-processed list. fs1 is the done list. *)
let rec skolemize_assumptions (fs0 : form list) (fs1 : form list) (e : typeEnv) : 
    (form list * form list * typeEnv) =
  match fs0 with
    | [] -> ([], fs1, e) (* done *)
    | f0 :: frest -> 
	let (il, _) = List.split e in
	let (f1, _)  = unique_variables (negation_normal_form f0) il in
	let (f2, e1) = skolemize f1 [] in
	  skolemize_assumptions frest (f2 :: fs1) (e @ e1)

let process_goal (f : form) : form * typedIdent list =
  let (f0, _) = unique_variables (negation_normal_form (mk_not f)) [] in 
  let (f1, til1) = skolemize f0 [] in
  (f1, til1)

(** Remove rtrancl and cardinality constraints from sequent *)
(** TODO: duplicate version in FolTranslate *)
let remove_rtrancl_card : sequent -> sequent =
  let non_fol_constants = 
    List.map (fun s -> (mk_var s, 1)) pseudo_constants @
    List.map (fun c -> (Const c, 1)) [Card; Cardeq; Cardleq; Cardgeq]
  in fun (s:sequent) ->
    let remove_smart = smart_abstract_constructs non_fol_constants in 
    let f0, _ = TypeReconstruct.reconstruct_types [] (form_of_sequent s) in
    let f = remove_smart f0 in
    sequent_of_form f 


(** Remove pointsto from sequent *)
let remove_pointsto (s : sequent) : sequent =
  let remove_smart = smart_abstract_constructs [(mk_var points_to_name, 3)] in
  let f = remove_smart (form_of_sequent s) in
  sequent_of_form f

(** Rewrite rule for removal of Ite *)
let rewrite_ite : rewriteRule =
  let r _ replace_map pol genv env t =
    let rec rewrite f  =
      match f with
      | App(Const Ite, [f0; f1; f2]) ->
	  (try (mk_var (fst (FormHashtbl.find replace_map f)), [])
	  with Not_found ->
	    let v = Util.fresh_name "ite" in
	    let v0 = Var v in
	    let f00, na0 = rewrite f0 in
	    let f10, na1 = rewrite f1 in
	    let f20, na2 = rewrite f2 in
	    let f11, defs0 = smt_form (FormUtil.smk_impl (f00, FormUtil.mk_eq(v0, f10))) [] in
	    let f21, defs1 = smt_form (FormUtil.smk_impl ((FormUtil.mk_not f00),
							     FormUtil.mk_eq(v0, f20))) defs0 in
	    let vdef = smk_and ([f11; f21] @ defs1) in	    
	    let new_var = mk_outer_forall pol f (mk_const_decl (v, TypeUniverse) (Some vdef)) in
	    let _ = FormHashtbl.add replace_map f (v, TypeUniverse) in
	    (v0, new_var :: na0 @ na1 @ na2))
      | App(f0, fl0) -> 
	  let f1, na0 = rewrite f0 in
	  let fl1, na1 = List.fold_right 
	      (fun f (fl1, new_vars) ->
		let f', new_vars' = rewrite f in
		(f'::fl1, new_vars' @ new_vars))  
	      fl0 ([], [])
	  in
	  (App(f1, fl1), na0 @ na1)
      | TypedForm (f', ty) -> 
	  let f'', na = rewrite f' in
	  (TypedForm (f'', ty), na)
      | _ -> (f, [])
    in rewrite t
  in (r, RewriteAtoms)

(** Rewrite rule that replaces predicates under rtrancl_pt by fresh predicate symbols *)
let rewrite_rtc : rewriteRule =
  let r call_back replace_map pol genv env f =
    let rec rewrite f =
      match f with
      | App(Var rtrancl, (Binder (Lambda, [(v1,ty1); (v2,ty2)], f') as p::args)) 
      | App(Var rtrancl, (Binder (Lambda, [(v1,ty1)], Binder (Lambda, [(v2,ty2)], f')) as p::args))
      | App(TypedForm (Var rtrancl, _), (Binder (Lambda, [(v1,ty1); (v2,ty2)], f') as p::args)) 
      | App(TypedForm (Var rtrancl, _), (Binder (Lambda, [(v1,ty1)], Binder (Lambda, [(v2,ty2)], f')) as p::args))
	when rtrancl = str_rtrancl ->
	  let p1, aux_vars =
	    try (mk_var (fst (FormHashtbl.find replace_map p)), [])
	    with Not_found ->
	      let vs = [(v1, ty1); (v2, ty2)] in
	      let p1_name = Util.fresh_name "rtc_p" in
	      let p1 = Var p1_name in
	      let p1_def0 = smk_foralls (vs, mk_iff(App(p1, [mk_var v1; mk_var v2]), f')) in	    
	      let p1_def, aux_vars' = call_back pol env p1_def0 in
	      let p1_type = TypeFun ([ty1; ty2], mk_bool_type) in
	      let new_var = mk_outer_forall pol p (mk_const_decl (p1_name, p1_type) (Some p1_def)) in
	      let _ = FormHashtbl.add replace_map p (p1_name, p1_type) in
	      (p1, new_var :: aux_vars')
	  in (App (Var str_rtrancl, (p1::args)), aux_vars)
      | _ -> (f, [])
    in rewrite f
  in (r, RewriteAtoms)

(* This procedure applies rewriter until a fixed point is reached.
   The rewriter should return the rewritten formula and flag that
   indicates whether the formula has changed.
*)
let rec fixed_point_rewrite (rewriter : form -> form * bool) (f : form): form =
  debug_msg ("fixed_point_rewrite: ");
  debug_msg ((PrintForm.string_of_form f) ^ "\n");
  let f0, changed = rewriter f in
    (* iterate until a fixed point is reached *)
    if (changed) then
      fixed_point_rewrite rewriter f0
    else f0

(* This pass rewrites the very simple case of an array read which either:
   (1) reads the result of the preceding write or
   (2) is orthogonal to the preceding write
   in a way in which we can determine this from the text of the formula.

   This pass is best used with fixed_point_rewrite, to handle cases such as:
   arrayRead (arrayWrite (arrayWrite a0 0 v0) a0 1 v1) a0 0

   In one pass, this would reduce to:
   arrayRead (arrayWrite a0 0 v0) a0 0

   whereas if we iterate to a fixed point, we would get: v0
*)
let rec simple_array_rewrite (f : form) : form * bool = 
  match f with
    | Var _ | Const _ -> f, false
    | App(App(Const ArrayWrite, [arrayState; array0; index0; val0]), [array1; index1]) 
	(* This is not the right way to do an array read, but let's handle it anyhow. *)
    | App(Const ArrayRead, [App(Const ArrayWrite, [arrayState; array0; index0; val0]); array1; index1])
	when (array0 = array1) ->
	begin
	  if (index0 = index1) then
	    let val1, _ = simple_array_rewrite val0 in
	      (val1, true)
	  else
	    match index0, index1 with
	      | Const (IntConst i), Const (IntConst j) ->
		  assert (not (i = j));
		  let as0, _ = simple_array_rewrite arrayState in
		  let a0, _ = simple_array_rewrite array0 in
		  let f0 = App(Const ArrayRead, [as0; a0; index1]) in
 		    (f0, true)
	      | _ ->
		  let args0, a0changed = List.split (List.map simple_array_rewrite [arrayState; array0; index0; val0]) in
		  let args1, a1changed = List.split (List.map simple_array_rewrite [array1; index1]) in
		  let changed = List.exists (fun(b) -> b) (a0changed @ a1changed) in
		    (App(Const ArrayRead, (App(Const ArrayWrite, args0) :: args1)), changed)
	end
    | App(f0, fl0) ->
	let f1, fchanged = simple_array_rewrite f0 in
	let fl1, flchanged = List.split (List.map simple_array_rewrite fl0) in
	let changed = fchanged || List.exists (fun(b) -> b) flchanged in
	  (App(f1, fl1), changed)
    | Binder(bk0, til0, f0) ->
	let f1, changed = simple_array_rewrite f0 in
	  (Binder(bk0, til0, f1), changed)
    | TypedForm _ ->
	(* There shouldn't be any typed formulas at this point. *)
	failwith ("simple_array_rewrite: can't handle " ^ (PrintForm.string_of_form f))

let simplify (goal : form) (assumptions : form list) : form * form list =
  let is_const_false (f : form) : bool = 
    (f = Const (BoolConst false)) in
  let not_const_false (f : form) : bool = 
    (f <> Const (BoolConst false)) in
  let is_const_true (f : form) : bool = 
    (f = Const (BoolConst true)) in  
  let not_const_true (f : form) : bool = 
    (f <> Const (BoolConst true)) in  
  let rec simplify_form (f : form) : form =
    match f with
      | App(Const Or, fs) ->
	  if (List.exists is_const_true fs) then
	    Const (BoolConst true)
	  else
	    let fs' = List.filter not_const_false fs in
	      if (fs' = []) then
		Const (BoolConst false)
	      else 
		App(Const Or, fs')
      | App(Const And, fs) ->
	  if (List.exists is_const_false fs) then
	    Const (BoolConst false)
	  else 
	    let fs' = List.filter not_const_true fs in
	      if (fs' = []) then
		Const (BoolConst true)
	      else
		App(Const And, fs')
      | App(f0, fs) ->
	  App((simplify_form f0), (List.map simplify_form fs))
      | Binder(b, til, f0) ->
	  Binder(b, til, (simplify_form f0))
      | TypedForm(f0, ty) ->
	  TypedForm((simplify_form f0), ty)
      | _ -> f in
  let rec split_assumption (f : form) : form list =
    match f with
      | App(Const And, fs0) -> 
	  List.flatten (List.map split_assumption fs0)
      | _ -> [f]
  in
  let goal = simplify_form (FormUtil.flatten goal) in
  let assumptions = List.map FormUtil.flatten assumptions in
  let assumptions = List.map simplify_form assumptions in
  let assumptions = List.flatten (List.map split_assumption assumptions) in
    (goal, assumptions)

(* SMTLIB reserved words *)
let keywords = ["assumption"; "extrafuns"; "extrapreds"; "extrasorts"; 
		"formula"; "logic"; "notes"; "status"; "store"; "select"]

let sanitize_keywords (f : form) : form =
  let rm = List.map (fun x -> (x, mk_var (Util.fresh_name x))) keywords in
    subst rm f

let process_sequent (o : options_t) (s0 : sequent) : (typeEnv * (form list) * form) =
  (* Remove rtrancl_pt and tree *)
  let s1 = if flag_positive o "KeepRtrancl" then s0 else remove_rtrancl_card s0 in 
  let s = if flag_positive o "KeepPointstos" then s1 else remove_pointsto s1 in 
  (* let _ = print_endline ( "\n" ^ string_of_sequent s) in *) 
  (* Eliminate free variables - substitute definition equality assumptions *)
  let s = elim_fv_in_seq false s in
  (* Get types *)
  let f = sanitize_booleans (FormUtil.form_of_sequent s) in
  let f = sanitize_keywords f in
  let f = match f with TypedForm _ -> f | _ -> TypedForm(f, TypeApp(TypeBool, [])) in
  let env0 = get_annotated_types f in
  (* Resolve ambiguous operators and remove lambda abstraction *)
  let f0 = disambiguate (unlambda ~keep_comprehensions:false f) in
  (* Rewrite rtrancl_pt if option KeepRtrancl is set *) 
  let f0, env0 = 
    let f1, env1 =
      if flag_positive o "KeepRtrancl" then
	try
	  if flag_positive o "Tree" then
	    let encTriggers = not (flag_positive o "NoTriggers") in
	    let assms, concl = sequent_of_form f0 in
	    let concl1, env1 = TermRewrite.rewrite true [rewrite_tree] env0 concl in
	    let f1 = form_of_sequent (assms, concl1) in
	    let f2 = RtranclTreesTranslation.rewrite_rtrancl (remove_comments f1) encTriggers in
	    f2, env1
	  else raise (Invalid_argument "")
	with Invalid_argument msg ->
	  if msg <> "" then Util.msg (msg ^ "\n");
	  let f1, env1 = TermRewrite.rewrite true [rewrite_tree] env0 f0 in
	  let f2 = if flag_positive o "PureList" then
	    PureListTranslation.rewrite_rtrancl (remove_comments f1) true
	  else
	    RtranclTranslation.rewrite_rtrancl (remove_comments f1) true 
	  in f2, env1
      else f0, env0
    in
    form_of_sequent (remove_rtrancl_card (sequent_of_form f1)), env1
  in
    (* Rewrite set expressions and higher order constructs *)
  let rewrite_rules =
    [rewrite_function_eq;
     rewrite_pointsto;
     rewrite_FieldRead_FieldWrite;
     (*rewrite_mod*)]
  in
  let _ = debug_msg ((PrintForm.string_of_form f0) ^ "\n\nApplying rewrite rules...\n") in
  let f1_0, env = TermRewrite.rewrite true rewrite_rules env0 f0 in
  let _ = debug_msg ((PrintForm.string_of_form f1_0) ^ "\n\nRewriting lambdas...\n") in  
  let f1_0 = rewriteLambdas (remove_typedform f1_0) in
  let f1, env = TypeReconstruct.reconstruct_types env f1_0 in
  let _ = debug_msg ((PrintForm.string_of_form f1) ^ "\n\nRewriting ite...\n") in  

    (** Rewrite ite statements into implications **)
  let f1, env = if !cvcl_rewrite_ite then
    TermRewrite.rewrite true [rewrite_ite] env (disambiguate f1) 
  else f1, env in
    (** Infer types for introduced ite variables. **)
  let f1, env = TypeReconstruct.reconstruct_types env f1 in

  let _ = debug_msg ((PrintForm.string_of_form f1) ^ "\n\nRewriting sets...\n") in
  let f12, env = TermRewrite.rewrite true [rewrite_sets] env (elim_quants f1) in
  let _ = debug_msg ((PrintForm.string_of_form f12) ^ "\n\nRewriting set elements...\n") in
  let f1, env = TermRewrite.rewrite_elems f12 env in
  let _ = debug_msg ((PrintForm.string_of_form f1) ^ "\n\nRewriting tuples...\n") in
  let f1, env = TermRewrite.rewrite_tuples (Hashtbl.create 10) f1 env in
  let _ = debug_msg ((PrintForm.string_of_form f1) ^ "\n\nRewriting into SMT...\n") in
  (* Remove types to make formulas easier to process. *)
  let f2, defs = smt_form 
    (fixed_point_rewrite simple_array_rewrite 
       (FormUtil.remove_typedform f1)) [] in
  let assumptions, to_prove = sequent_of_form f2 in
  let f20 = form_of_sequent (assumptions @ defs, to_prove) in
    (** Rewrite Ite's introduced by smt_form *)
  let f21, env = if !cvcl_rewrite_ite then
    TermRewrite.rewrite true [rewrite_ite] env f20 
  else f20, env in
    (** Get types for variables introduced by rewriting Ite's *)
  let f22, env = TypeReconstruct.reconstruct_types env f21 in
  let fs, rhs = sequent_of_form (unnotate_all_types (disambiguate f22)) in
  let _ = debug_msg ((PrintForm.string_of_form rhs) ^ "\n\nProcessing goal...\n") in
  let f3, sfs = process_goal rhs in
  let _ = debug_msg ((PrintForm.string_of_form f3) ^ "\n\nSkolemizing assumptions...\n") in
  let _, fs0, env0 = skolemize_assumptions fs [] (sfs @ env) in
  let f3, fs0 = simplify f3 fs0 in
  let final_fv = fv (form_of_sequent (fs0, f3)) in
  let env0 = List.filter (fun (s, _) -> List.mem s final_fv) env0 in 
  let env0 = process_formula (process_assumptions env0 fs0) f3 in
    (env0, fs0, f3)
