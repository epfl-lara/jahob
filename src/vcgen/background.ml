(** Background formula for verification conditions *)

open Common
open Ast
open AstUtil
open Form
open FormUtil

let get_ref_fields (prog : program) : ident list = 
  let get_field (fdef : field_def) : ident = fdef.field_name in
    List.map get_field prog.p_ref_fields

let get_static_refs (prog : program) : ident list =
  let get_static (gs : ident list) (gd : global_def) : ident list = 
    match gd.global_type with
      | "int" | "boolean" -> gs
      | _ -> gs @ [gd.global_name]
  in
    List.fold_left get_static [] prog.p_globals

let get_static_vars (prog : program) (im : impl_module) : ident list =
  let imn = im.im_name in
  let select (gd : global_def) = 
    (let name = gd.global_name in
      if Util.unqualify_getting_module name = imn then [name]
      else [])
  in
    List.concat (List.map select prog.p_globals)

(** null..f = null *)
let get_null_derefs (prog : program) : form list =
  let fields = get_ref_fields prog in
  let mk_deref (fd : ident) : form =
    mk_eq(mk_fieldRead (mk_var fd) mk_null,mk_null)
  in 
    List.map mk_deref fields

let rec mk_arr_pt ((tids, f, ty) : (typedIdent list * form * array_type)) : 
    (typedIdent list * form) list =
  let iid = "i" ^ (string_of_int (List.length tids)) in
  let tids' = tids @ [(iid, mk_int_type)] in
  let ivar = mk_var iid in
  let f' = mk_arrayRead1 f ivar in
    match ty with
      | BaseType id -> 
	  if id = "int" || id = "boolean" then 
	    []
	  else 
	    [(tids', mk_elem (f', mk_var id))]
      | ArrayType at ->
	  (tids', mk_elem (f', mk_var arrayName))::mk_arr_pt (tids', f', at)
	    
let mk_array_points_to (fd : field_def) (at : array_type) : form =
  let xid = "x" in
  let xvar = mk_var xid in
  let f = mk_fieldRead (mk_var fd.field_name) xvar in
  let lhs = mk_elem(xvar, mk_var (obj_var fd.field_from)) in
  let mk_constraint ((tids, f) : (typedIdent list * form)) : form =
    mk_comment "array_pointsto"
      (mk_forall (xid, mk_object_type, (smk_impl(lhs, mk_foralls (tids, f)))))
  in
    smk_and (List.map mk_constraint (mk_arr_pt ([], f, at)))

let mk_static_array_points_to (gd : global_def) (at : array_type) : form =
  let mk_constraint ((tids, f) : (typedIdent list * form)) : form =
    mk_comment "static_pointsto" (mk_foralls (tids, f))
  in
    smk_and (List.map mk_constraint (mk_arr_pt ([], mk_var gd.global_name, at)))

(** class C {D f} generates constraint x : C --> f x : D *)
let get_points_to (prog : program) (ids : ident list) : form list =
  let get_pt (f : field_def) : form =
    let points_to = 
      mk_comment "field_pointsto" 
	(mk_points_to 
	   (mk_var (obj_var f.field_from))
	   (mk_var f.field_name)
	   (mk_var (obj_var f.field_to))) in
      match f.field_basetype with
	| None -> points_to
	| Some at -> 
	    let arr_pt = mk_array_points_to f at in
	      smk_and [points_to; arr_pt] in
  let is_relevant (fd : field_def) : bool =
    List.mem fd.field_name ids
  in
    List.map get_pt (List.filter is_relevant prog.p_ref_fields)

(** if a global variable x has type T, generate formula x:T *)
let get_global_type_info (prog : program) : form list =
  let get_ti (g : global_def) : form =
    let points_to =
      mk_comment "static_pointsto" 
	(mk_elem(mk_var g.global_name, mk_var g.global_type)) in
      match g.global_basetype with
	| None -> points_to
	| Some at ->
	    let arr_pt = mk_static_array_points_to g at in
	      smk_and [points_to; arr_pt]
  in 
    List.map get_ti prog.p_globals

(** !! Fix this to include non-flat hierarchy! *)
let mk_class_hierarchy (cns0 : ident list) : form list = 
  let cns = List.filter (fun x -> x <> Jast.objectName) cns0 in
  let _ = Debug.msg ("CLASS HIERARCHY OF: " ^ String.concat " " cns) in
  let mk_disjoint c1 c2 = 
    mk_eq(mk_cap(mk_var c1,mk_var c2),mk_finite_set [mk_null]) in
  let rec all_pairs fs ci cj =
    match ci with
      | ci0::ci1 ->
	  (match cj with
	     | cj0::cj1 -> 
		 all_pairs 
		   ((mk_disjoint ci0 cj0)::fs)
		   ci
		   cj1
	     | [] -> (match ci1 with
			| ci10::ci11 -> all_pairs fs ci1 ci11
			| [] -> fs))
      | [] -> fs
  in
  let x = "xObj" in
  let universal = mk_forall(x,mk_object_type,mk_elem(mk_var x,mk_var Jast.objectName)) in
  let subsets = [universal] in
  let disjointness = all_pairs [] (""::cns) [] in 
  let res = subsets @ disjointness in
  let _ = Debug.msg ("CLASS HIERARCHY RESULT: " ^ 
		       PrintForm.wr_form_list ", " res) in
    res

(** Unallocated objects (and, as a result, just allocated) objects,
    have all reference fields null and no field points to them.
    Their owners are token.NoOwner *)

let get_unalloc_lonely_xid
    (prog : program) 
    (xid : ident) (* object itself *) 
    : form =
  let xvar = mk_var xid in
  let yid = "y" in
  let yvar = mk_var yid in
  let fds = get_ref_fields prog in
  let mk_not_pointed f = 
    mk_forall(yid,
	      mk_object_type,
	      mk_neq(mk_fieldRead (mk_var f) yvar, xvar)) in
  let not_pointed = List.map mk_not_pointed fds in (* y..f ~= null *)
  let global_not_pointed = 
    List.map (fun f -> mk_neq (mk_var f, xvar)) (get_static_refs prog) in
  let zid = "z" in
  let zvar = mk_var zid in
  let iid = "i" in
  let ivar = mk_var iid in
  let not_pointed_array =
    [mk_foralls([(zid, mk_object_type); (iid, mk_int_type)],
	       mk_neq(mk_arrayRead1 zvar ivar, xvar))] in
  let mk_field_null f = 
    mk_eq(mk_fieldRead (mk_var f) xvar, mk_null) in
  let fields_null = List.map mk_field_null fds in (* x..f = null *)
  let jid = "j" in
  let jvar = mk_var jid in
  let elems_null = 
    [mk_forall(jid, mk_int_type, mk_eq(mk_arrayRead1 xvar jvar, mk_null))] in
  let token_none = (* x..Object.owner = token.NoOwner *)
    if !CmdLine.tokens then
     [mk_eq(mk_owner_of xvar,
	    mk_var (mk_class_token_name no_owner_name))]
    else []
  in
    smk_and (not_pointed @ not_pointed_array @ global_not_pointed @
	       token_none @ fields_null @ elems_null)

let get_unalloc_lonely (prog : program) : form =
  let xid = "x" in
  let xvar = mk_var xid in
    mk_comment "unalloc_lonely"
      (smk_forall(xid,mk_object_type,
		  smk_impl(mk_notelem(xvar, all_alloc_objsf),
			   get_unalloc_lonely_xid prog xid)))

(** class hierarchy; 
    following allocated object leads 
    to allocated object of the right type *)
let get_alloc_conditions (prog : program) (im : impl_module) (fvs : ident list) : form list =
  let class_names = get_class_names prog in
  let class_hierarchy = mk_class_hierarchy class_names in
  let null_alloc = [mk_elem(mk_null,all_alloc_objsf)] in (** null : alloc.Object *)
  let is_alloc id = mk_elem(mk_var id, all_alloc_objsf) in 
  let static_vars_alloc = List.map is_alloc (get_static_vars prog im) in (** static variables are allocated *)
  let points_to = get_points_to prog fvs in
  let unalloc_lonely = [get_unalloc_lonely prog] in
    class_hierarchy @ null_alloc @ static_vars_alloc @ points_to @ 
      unalloc_lonely

(** axioms stating that class ownership tokens are distinct *)
let get_token_axioms (prog : program) : form list =
  let cns = no_owner_name :: get_class_names prog in
  let mk_distinct c1 c2 = 
    mk_neq(mk_typedform(mk_var (mk_class_token_name c1), mk_object_type),
			mk_var (mk_class_token_name c2)) in
  let rec all_pairs fs ci cj =
    match ci with
      | ci0::ci1 ->
	  (match cj with
	     | cj0::cj1 -> 
		 all_pairs 
		   ((mk_distinct ci0 cj0)::fs)
		   ci
		   cj1
	     | [] -> (match ci1 with
			| ci10::ci11 -> all_pairs fs ci1 ci11
			| [] -> fs))
      | [] -> fs
  in
  let res = all_pairs [] (""::cns) [] in
  let _ = Debug.msg ("token axiom result: " ^ 
		       PrintForm.wr_form_list ", " res) in
    res

let add_background_form
    (prog : program)
    (im : impl_module)
    (f : form) : form =

  let fvs = fv f in
  let perhaps fs = if !CmdLine.background then fs else [] in

  let free_invariants =
    let not_current (sm : spec_module) = (sm.sm_name <> im.im_name) in
    let get_free_inv (sm1 : spec_module) = 
      ListLabels.map ~f:(fun i -> App (Const Comment, [Const (StringConst ("FreeInv " ^ i.Specs.inv_name)); i.Specs.inv_form])) 
	sm1.sm_free_invs in
      List.concat (List.map get_free_inv (List.filter not_current prog.p_specs)) in

  let global_types = get_global_type_info prog in
  let alloc_conditions = perhaps (get_alloc_conditions prog im fvs) in
  let null_derefs = perhaps (get_null_derefs prog) in
  let token_axioms = 
    if !CmdLine.tokens then perhaps (get_token_axioms prog) 
    else []
  in

  let f1 = smk_impl
    ((smk_and 
       (free_invariants @
	  null_derefs @	  
          alloc_conditions @
	  global_types @
	  token_axioms)),
     f) in
    f1

(** End background formula *)
