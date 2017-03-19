open Bf
open Bf_set
open Form
open FormUtil
open PrintForm
open TypeReconstruct
open BohneUtil   

(** Predicates *)   
type pred = Bf.var

(** Predicate properties *)
type pred_props =
  | IsSingleton of typedIdent option
  | IsNull
  | IsConst
  | IsOld of ident
  | Inherit of Ast.program_point list
  | DependsOn of ident list
 
(** Predicate declaration *)
type pred_decl = {
    pred_name : ident;
    pred_index : pred;
    pred_def : form;
    pred_concr_def : form;
    pred_dep_vars : ident list;
    pred_env : typeEnv;
    pred_arity : int;
    pred_props : pred_props list
  }

let empty_cubes = ref Bf.bottom

let var_prefix = ""
	
let free_var_prefix = "v"

let bound_var_prefix = "v_"

let null_name = var_prefix ^ (string_of_const NullConst)

let var_name name k = var_prefix ^ name ^ string_of_int k
         
let free_var_name k = var_name free_var_prefix k

let var name k = mk_var (var_name name k)

let free_var k = mk_var (free_var_name k)

let typed_var name k = (var_name name k, mk_object_type)

let var_list name arity =
  let rec l acc = function
    | 0 -> acc
    | k -> l (var_name name (k - 1) :: acc) (k - 1)
  in l [] arity

let free_var_list = var_list free_var_prefix

let bound_var_list = var_list bound_var_prefix

let typed_free_var k = (free_var_name k, mk_object_type)

let typed_var_list name arity =
 let rec l k acc = 
   if k > 0 then l (k-1) (typed_var name (k-1)::acc) else acc
 in l arity []	

let typed_free_var_list arity =
 let rec l k acc = 
   if k > 0 then l (k-1) (typed_free_var (k-1)::acc) else acc
 in l arity []

let free_var_index var =
  let index_start = String.length var_prefix + String.length free_var_prefix in
  let index_string = String.sub var index_start (String.length var - index_start) in
  int_of_string index_string

let pred_prefix = "p__"

let merge_props props1 props2 =
  let find_inherited props = 
    try Util.find_map (function Inherit pps -> Some pps | _ -> None) props
    with Not_found -> []
  in
  let inherited_pps = Util.union (find_inherited props1) (find_inherited props2) in
  Inherit inherited_pps :: List.filter (function Inherit _ -> false | _ -> true) props1

(** Construct new predicate declaration *)
let mk_pred_decl pname pdef0 props =
  let i = Bf.new_var () in
  let pdef, env = reconstruct_types [] (transform_old pdef0) in 
  let ty = TypeReconstruct.get_type env pdef in
  let mk_singleton (t, ty) =
    let opt_vt = match strip_types t with 
    | Var v -> Some (v, ty)
    | _ -> None
    in IsSingleton opt_vt
  in
  let pdef', props = 
    if ty = mk_object_type then
      Binder (Comprehension, [typed_var bound_var_prefix 0], 
	      mk_eq (pdef, var bound_var_prefix 0)),
      mk_singleton (pdef, ty) :: props
    else if ty = mk_bool_type then
      pdef, props
    else match unnotate_all_types pdef with
    | Binder (Comprehension,[(v1, ty)], App (Const Eq, [t; Var v2])) when v1 = v2 ->
	pdef, mk_singleton (t, ty) :: props
    | _ -> pdef, props
  in
  let arity, pdef' = match pdef' with 
  | Binder (Comprehension, vs, f) ->
      let arity = List.length vs in
      let vs', smap, _ = List.fold_right 
	  (fun (v, t) (vs', smap, k) -> 
	    let v' = var_name bound_var_prefix k in
	    ((v', t)::vs', (v, mk_var v')::smap, k - 1)) 
	  vs ([], [], arity - 1)
      in 
      (arity, unlambda (Binder (Comprehension, vs', subst smap f)))
  | _ -> 
      (* assert (ty = TypeApp(TypeBool, [])); *)
      (0, pdef')
  in
  let vars = List.map (fun (x, ty) -> TypedForm (mk_var x, ty)) (typed_free_var_list arity) in
  let elem = match vars with [x] -> x | _ -> mk_tuple vars in
  let concr_pdef = 
    if arity > 0 then
      unlambda ~keep_comprehensions:false (mk_elem (elem, pdef'))
    else pdef'
  in
  let dep_vars = Util.intersect (fv concr_pdef) (free_var_list arity) in
  { pred_name = pname;
    pred_index = i;
    pred_def = pdef';
    pred_concr_def = concr_pdef;
    pred_dep_vars = dep_vars;
    pred_env = env;
    pred_arity = arity;
    pred_props = props
  }



(** Predicate for null *)

let mk_null_decl () =
  mk_pred_decl (pred_prefix ^ null_name)
    (Binder (Comprehension, [typed_var bound_var_prefix 0], 
	     App (Const Eq, [Const NullConst; var bound_var_prefix 0])))
    [IsSingleton None; IsNull; IsConst]

let null_decl = mk_null_decl ()

(** Index of null predicate *)
let null_pred = null_decl.pred_index

(** Array containing all predicate declarations *)
let predicates = Array.make Bf.var_max null_decl

let _ = predicates.(0) <- null_decl

(** Maximal predicate index *)
let max_index () = Bf.vars () - 1

let find_preds f = 
  let rec search i =
    if i < 0 then raise Not_found
    else if f predicates.(i) then predicates.(i)
    else search (i - 1)
  in search (max_index ())

let search name = find_preds (fun p -> p.pred_name = name)

let eq_preds p1 p2 =
  p1.pred_index = p2.pred_index

let diff_preds preds1 preds2 =
  List.filter (fun p -> List.for_all (fun q -> q.pred_index <> p.pred_index) preds2) preds1

let in_preds p preds = 
  List.exists (fun p' -> p'.pred_index = p.pred_index) preds

let has_prop pprop p =
  List.mem pprop p.pred_props

let inherits p =
  List.exists (function Inherit [] -> false | Inherit _ -> true | _ -> false) p.pred_props

let inherits_to pp p =
  List.exists (function Inherit pps -> List.mem pp pps | _ -> false) p.pred_props

let is_singleton p =
  List.exists (function IsSingleton _ -> true | _ -> false) p.pred_props

let is_variable p =
  List.exists (function IsSingleton (Some _) -> true | _ -> false) p.pred_props

let is_old p =
  List.exists (function IsOld _ -> true | _ -> false) p.pred_props

let is_state_pred p =
  p.pred_arity = 0

let get_pred_name i = predicates.(i).pred_name

let get_pred_decl i = predicates.(i)

(** Get predicate by name *)
let pred_by_name name =
  try search name
  with Not_found ->
    Util.warn (Printf.sprintf "Could not find predicate '%s'" name); 
    raise Not_found

let pred_type pred =
  match pred.pred_arity with
  | 0 -> mk_bool_type
  | 1 -> mk_set_type mk_object_type
  | n -> 
      let elem_ty = TypeProd (Util.generate_list (fun _ -> mk_object_type) n) in
      mk_set_type elem_ty

let pred_to_form =
  let hash_cons_map = Hashtbl.create Bf.var_max in
  fun concretize p ->
    try Hashtbl.find hash_cons_map (concretize, p)
    with Not_found ->
      let p_form = 
	if concretize || is_singleton p then p.pred_concr_def else 
	let vars = List.map (fun (x, _) -> mk_var x) (typed_free_var_list p.pred_arity) in
	let elem = match vars with [x] -> x | _ -> mk_tuple vars in
	if is_state_pred p then
	  TypedForm (mk_var p.pred_name, mk_bool_type)
	else mk_elem (elem, TypedForm (mk_var p.pred_name, pred_type p))
      in
      Hashtbl.add hash_cons_map (concretize, p) p_form;
      p_form

let get_all_preds () = 
  let rec get_all i acc =
    if i = -1 then acc
    else get_all (i - 1) (predicates.(i)::acc)
  in 
  get_all (max_index ()) []

let get_pred_def pred = 
  let pred_ty = pred_type pred in
  mk_eq (TypedForm (mk_var (pred.pred_name), pred_ty), pred.pred_def)
  
let get_pred_free_vars pred =
  free_var_list pred.pred_arity

let get_pred_defs preds =
  List.fold_left (fun acc p ->
    if is_singleton p || equal p.pred_def (mk_var p.pred_name) then acc 
    else get_pred_def p::acc) [] preds

let get_all_defs () = 
  get_pred_defs (get_all_preds ())


let compute_empty_cubes p1 =
  (* if not !CmdLine.useheuristics then Bf.bottom else *)
  (* restrict to cubes of length 2 *
   * cubes that are only build from singletons are never empty *)
  let p1_def = pred_to_form true p1 in
  let p1_var = Bf.mk_var p1.pred_index in
  (* let entails f1 f2 =
    BfCachedDecider.decide trivial_context (smk_impl (f1, f2))
  in *)
  let new_empty = List.fold_left 
    (fun acc p2 ->
      if eq_preds p1 p2 then acc else
      let p2_def = pred_to_form true p2 in
      let p2_var = Bf.mk_var p2.pred_index in
      if entails_synt p1_def p2_def then
	Bf.disj acc (Bf.conj (Bf.neg p2_var) p1_var)
      else if entails_synt p2_def p1_def then
	Bf.disj acc (Bf.conj (Bf.neg p1_var) p2_var)
      else if entails_synt (smk_not p1_def) p2_def then
	Bf.disj acc (Bf.conj (Bf.neg p1_var) (Bf.neg p2_var))
      else if entails_synt p2_def (smk_not p1_def) then
	Bf.disj acc (Bf.conj p2_var p1_var)
      else acc) !empty_cubes (get_all_preds ())
  in
  empty_cubes := new_empty

(** Add a predicate *)
let add_pred_decl name pdef props =
  try 
    let pred = search name in
    {pred with pred_props =  merge_props pred.pred_props props}
  with Not_found -> 
    let decl = mk_pred_decl name pdef props in
    predicates.(decl.pred_index) <- decl;
    (* compute_empty_cubes decl; *)
    decl

(** Add a predicate for some variable *) 
let add_var_pred_decl pp ((ident, ty) as vt) =
  try
    let p = find_preds 
	(fun p -> 
	  List.exists (function 
	    | IsSingleton (Some vt') -> vt = vt' 
	    | _ -> false) p.pred_props)
    in {p with pred_props = merge_props p.pred_props [Inherit [pp]]}
  with Not_found -> 
    let name, def, props = 
      match ty with
      | TypeApp (TypeBool, []) -> (ident, mk_var ident, [])
      | TypeApp (TypeObject, []) ->
	  (pred_prefix ^ ident, Binder (Comprehension, [typed_var bound_var_prefix 0], 
					mk_eq (mk_var ident, var bound_var_prefix 0)),
	   [IsSingleton (Some vt)])
      | TypeApp (TypeSet, [TypeApp (TypeObject, [])]) ->
	  (ident, Binder (Comprehension, [typed_var bound_var_prefix 0],
			  mk_elem (var bound_var_prefix 0, mk_var ident)), [])
      | _ -> 
	  Util.warn ("Pred.mk_var_pred: unsupported type " ^ string_of_type ty); 
	  (pred_prefix ^ ident, mk_true, [])
    in
    add_pred_decl name def (Inherit [pp] :: props)

let sort_preds = List.stable_sort (fun p p' -> compare p.pred_index p'.pred_index)

let union_preds preds1 preds2 =
  let rec merge acc preds1 preds2 = 
    match preds1, preds2 with 
    | [], preds
    | preds, [] -> acc @ preds
    | p :: preds1', q :: preds2' when p.pred_index = q.pred_index ->
	let p' = {p with pred_props = merge_props p.pred_props q.pred_props} in
	merge (p' :: acc) preds1' preds2'
    | p :: preds1', q :: preds2' when p.pred_index > q.pred_index ->
	merge (q :: acc) preds1 preds2'
    | p :: preds1', q :: preds2' when p.pred_index < q.pred_index ->
	merge (p :: acc) preds1' preds2
    | _ -> failwith "empty match case"
  in
  merge [] (sort_preds preds1) (sort_preds preds2)
 
let reset () = 
  Bf.reset ();
  empty_cubes := Bf.bottom;
  ignore (Bf.new_var ())
  

let get_ident p =
  Util.find_map (function IsSingleton i -> i | _ -> None) p.pred_props

let get_deps p =
  try
    Util.find_map 
      (function DependsOn ps -> Some ps | _ -> None) 
      p.pred_props
  with Not_found -> []

let get_pred_by_def f = 
  let rec lookup i =
    if i = -1 then raise Not_found
    else if equal predicates.(i).pred_def (unlambda f)
         || equal (unlambda ~keep_comprehensions:false predicates.(i).pred_def) (unlambda f)  
         || equal predicates.(i).pred_concr_def (unlambda f)
    then predicates.(i)
    else lookup (i - 1) 
  in lookup (max_index ())

(** Add an unnamed predicate *)
let add_pred =
  let c = ref (-1) in
  fun pdef props ->
    try 
      let pred = get_pred_by_def pdef in
      {pred with pred_props = merge_props pred.pred_props props}
    with Not_found ->
      let pname = 
	c := !c + 1; 
	pred_prefix ^ (string_of_int !c)
      in 
      Debug.print_msg 4 (fun chan ->
	output_string chan ("\nadd predicate: " ^ string_of_form (mk_eq (mk_var pname, pdef)) ^ "\n"));
      add_pred_decl pname pdef props

let unold_pred p = pred_by_name (Util.find_map (function IsOld p -> Some p | _ -> None) p.pred_props)
	
let concretize_preds f =
  smk_impl (smk_and (get_all_defs ()), f)

let match_form preds unifiable fv f =
  List.fold_left (fun matches p ->
    let pdef = pred_to_form true p in
    let fvars = unifiable @ free_var_list p.pred_arity in
    match is_unifiable [] fvars pdef f with
    | true, mgu ->
	let vs = List.fold_left 
	    (fun acc (v, t) ->
	      match unnotate_all_types t with
	      | Var v' when List.mem v' fv -> acc
	      | _  ->
		  let arity =
		    (try free_var_index v with Failure _ -> 0) + 1
		  in
		  let bvs = typed_free_var_list arity in
		  let def = Binder (Comprehension, bvs, mk_eq (t, (TypedForm (mk_var v, mk_object_type)))) in
		  let new_p = add_pred def [] in
		  new_p :: acc) 
	    [] mgu
	in (vs, p) :: matches
    | _ -> matches) [] preds
 
let form_to_preds fv pdef =
  let matches = match_form (get_all_preds ()) [] fv pdef in
  try 
    Util.find_map 
      (function 
	| ([], p) -> Some ([], p)
	| _ -> None) matches
  with Not_found ->
    match matches with
    | (ps, p) :: _ -> (ps, p)
    | _ -> raise Not_found
  
   
let print_pred_decl chan pdecl =
  let out = output_string chan in
  let print_props props =
    out " [";
    if List.mem IsConst props then out "isConst, "
    else out "~isConst, ";
    (try
      let v_opt = Util.find_map (function IsSingleton v_opt -> Some v_opt | _ -> None) props  in
      Printf.fprintf chan "isSingleton %s, " (fst (Util.safe_unsome ("_", mk_object_type) v_opt))
    with Not_found -> out "~isSingleton, ");
    if List.exists (function IsOld _ -> true | _ -> false) props 
    then out "isOld, "
    else out "~isOld, ";
    (try 
      let inherit_to_pp = Util.find_map (function Inherit i -> Some i | _ -> None) props in
      out "inherit to: {";
      List.iter (fun pp -> Printf.fprintf chan "%d, " pp.Ast.pp_id) inherit_to_pp;
      out "}, ";
    with Not_found -> ());
    (try 
      let deps = Util.find_map (function DependsOn deps -> Some deps | _ -> None) props in
      out "depends on: {";
      List.iter (Printf.fprintf chan "%s, ") deps;
      out "}, ";
    with Not_found -> ());
    Printf.fprintf chan "index: %d]\n" pdecl.pred_index;
  in
  out (PrintForm.string_of_form (App (Const MetaEq, [mk_var pdecl.pred_name; pdecl.pred_def])));
  out "\n\t"; print_props pdecl.pred_props

