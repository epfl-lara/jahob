open Ast
open AstUtil
open Form
open FormUtil
open Util

let debug_id = Debug.register_debug_module "Static"
let debug_msg = Debug.debug_msg debug_id
let debug_lmsg = Debug.debug_lmsg debug_id

type tval = TPublic | TReturned | TPrivate

type esc_type =
  | PrimET                   (** primitive **)
  | NullET                   (** null is special **)
  | EmptyET                  (** empty set is special **)
  | ArrStET                  (** arrayState is special **)
  | ObjET of tval * esc_type option (** objects (and array elements) **)
  | SetET of esc_type        (** set elements **)
  | TupET of esc_type list   (** tuple elements **)
  | FunET of esc_type * esc_type (** function **)

type context = {
  ret_type : esc_type option;
  arg_types : esc_type list;
}
    
type work = {
  w_mname : ident; (** name of module to which method belongs **)
  w_method : proc_def;
  w_context : context;
}

type m_proc_def = ident * proc_def
 
type a_result = 
  | Succeed of context
  | Fail

type m_summary = context * a_result

type call_graph = (ident, m_proc_def list) Hashtbl.t

type m_cache = (ident, m_summary list) Hashtbl.t
    
let rec string_of_esc_type (et : esc_type) : string =
  match et with
    | PrimET -> "primitive"
    | NullET -> "null"
    | EmptyET -> "emptyset"
    | ArrStET -> "arrayState"
    | ObjET (tv, eto) -> 
	(match tv with
	   | TPublic -> "esc obj"
	   | TReturned -> "ret obj"
	   | TPrivate -> "unesc obj") ^
	  (match eto with
	     | Some et -> " [" ^ string_of_esc_type et ^ "]"
	     | _ -> "")
    | SetET et' -> "set {" ^ string_of_esc_type et' ^ "}"
    | TupET ets -> 
	"tuple (" ^ (String.concat ", " (List.map string_of_esc_type ets)) ^ ")"
    | FunET (et1, et2) ->
	"(" ^ (string_of_esc_type et1) ^ " => " ^ (string_of_esc_type et2) ^ ")"

(*
let mk_obj_ty (escapes : bool) : esc_type =
  let tv = if escapes then TPublic else TPrivate in
    ObjET (tv, None)

let mk_arr_ty (escapes : bool) (elem_ty : esc_type) : esc_type =
  let tv = if escapes then TPublic else TPrivate in
    ObjET (tv, Some elem_ty)
*)
  
let rec mk_escaped (et : esc_type) : esc_type =
  match et with
    | ObjET (tv, eto) -> 
	let eto' = match eto with
	  | Some et -> Some (mk_escaped et)
	  | _ -> None
	in
	  ObjET (TPublic, eto')
    | SetET et' -> SetET (mk_escaped et')
    | TupET ets -> TupET (List.map mk_escaped ets)
    | FunET (et1, et2) -> FunET (mk_escaped et1, mk_escaped et2)
    | PrimET -> PrimET
    | _ -> failwith ("mk_escaped did not expect: " ^ 
		       (string_of_esc_type et) ^ "\n")

let rec mk_returned (et : esc_type) : esc_type =
  match et with
    | ObjET (tv, eto) -> 
	let eto' = match eto with
	  | Some et -> Some (mk_returned et)
	  | _ -> None
	in
	  (match tv with
	     | TPublic -> ObjET (TPublic, eto')
	     | _ -> ObjET (TReturned, eto'))
    | SetET et' -> SetET (mk_returned et')
    | TupET ets -> TupET (List.map mk_returned ets)
    | FunET (et1, et2) -> FunET (mk_returned et1, mk_returned et2)
    | PrimET -> PrimET
    | _ -> failwith ("mk_returned did not expect: " ^ 
		       (string_of_esc_type et) ^ "\n")

let mk_unescaped (et : esc_type) : esc_type =
  match et with
    | ObjET (_, eto) -> ObjET (TPrivate, eto)
    | PrimET -> PrimET
    | _ -> failwith ("mk_unescaped did not expect: " ^ 
		       (string_of_esc_type et) ^ "\n")

let mk_unescaped_arr_and_elem (et : esc_type) : esc_type =
  match et with
    | ObjET (_, Some et) -> ObjET (TPrivate, Some (mk_unescaped et))
    | _ -> failwith ("mk_unescaped_arr_elem did not expect: " ^ 
		       (string_of_esc_type et) ^ "\n")

let is_concrete_vd (vd : var_decl) : bool =
  not vd.vd_abstract

(*
let get_owned_fields_of 
    (prog : program) 
    (owner : impl_module) 
    (impl : impl_module) : var_decl list =
  let spec = must_find_sm impl.im_name prog in
  let _ = List.iter
    (fun x -> 
       print_string ("[impl]: " ^ (PrintAst.pr_var_decl x) ^ "\n"))
    impl.im_vars in
  let _ = List.iter
    (fun x -> 
       print_string ("[spec]: " ^ (PrintAst.pr_var_decl x) ^ "\n"))
    spec.sm_spec_vars in
  let all_fields = Util.union impl.im_vars spec.sm_spec_vars in
    (*
      let concrete_fields = List.filter is_concrete_vd all_fields in
      concrete_fields
    *)
    all_fields

let get_owned_fields (prog : program) (owner : impl_module) : var_decl list =
  let owned_classes = impl_modules_claimed_by owner prog in
  let _ = List.iter 
    (fun x -> print_string ("Claims class " ^ x.im_name ^ "\n"))
    owned_classes in
    List.flatten (List.map (get_owned_fields_of prog owner) owned_classes)
*)

let get_field_type (vd : var_decl) : typeForm =
  match vd.vd_type with
    | TypeApp(TypeArray, [(TypeApp(TypeObject, [])); ty']) -> ty'
    | _ -> failwith 
	("Unexpected type: " ^ (PrintForm.string_of_type vd.vd_type) ^ "\n")

let is_impl (id : ident) (impl : impl_module) : bool =
  id = impl.im_name

let is_spec (id : ident) (spec : spec_module) : bool =
  id = spec.sm_name

let is_valid_class (prog : program) (id : ident) : bool =
  List.exists (is_impl id) prog.p_impls ||
    List.exists (is_spec id) prog.p_specs

let rec esc_type_of_array_type 
    (prog : program) 
    (ty : array_type) 
    (escapes : tval) : esc_type =
  match ty with
    | BaseType "int" 
    | BaseType "boolean" -> PrimET
    | BaseType id -> 
	if is_valid_class prog id then
	  ObjET (escapes, None)
	else
	  failwith ("Unrecognized base type: " ^ id ^ "\n")
    | ArrayType ty' -> 
	let elem_ty = esc_type_of_array_type prog ty' escapes in
	  ObjET (escapes, Some elem_ty)

let rec initial_value_of_type1
    (prog : program) 
    (bt : array_type option) 
    (escapes : tval) 
    (tf : typeForm) : esc_type =
  let initial_value = initial_value_of_type1 prog None escapes in
  let result = match bt with
    | None ->
	(match tf with
	   | TypeApp(TypeInt, [])
	   | TypeApp(TypeBool, []) -> PrimET
	   | TypeApp(TypeObject, []) -> ObjET (escapes, None)
	   | TypeApp(TypeSet,[tf']) -> 
	       SetET (initial_value tf')
	   | TypeProd tfs -> 
	       TupET (List.map initial_value tfs)
	   | TypeFun([tf1], tf2) ->
	       let ival1 = initial_value tf1 in
	       let ival2 = initial_value tf2 in
		 FunET (ival1, ival2)
	   | TypeFun(tf1::tfs, tf2) ->
	       let ival1 = initial_value tf1 in
	       let ival2 = initial_value (TypeFun(tfs, tf2)) in
		 FunET (ival1, ival2)
	   | _ -> failwith 
	       ("Unrecognized typeForm: " ^ 
		  (MlPrintForm.string_of_type tf) ^ "\n"))
    | Some ty -> ObjET (escapes, Some (esc_type_of_array_type prog ty escapes))
  in
    result

let initial_value_of_type
    (prog : program)
    (bt : array_type option)
    (escapes : bool)
    (tf : typeForm) : esc_type =
  let tv = if escapes then TPublic else TPrivate in
    initial_value_of_type1 prog bt tv tf

let is_field_def (id : ident) (fd : field_def) : bool =
  id = fd.field_name

let is_global_def (id : ident) (gd : global_def) : bool =
  id = gd.global_name

let is_static_field (vd : var_decl) : bool =
  not vd.vd_field

let initial_value_of_field 
    (prog : program) (vd : var_decl) (escapes : bool) : esc_type =
  let tf = if is_static_field vd then
    vd.vd_type else get_field_type vd in
    initial_value_of_type prog vd.vd_basetype escapes tf

let is_public_var_decl (prog : program) (vd : var_decl) : bool =
  match Util.split_by "." vd.vd_name with
    | [mname;_] ->
	(match find_sm mname prog with
	   | Some sm ->
	       (match find_var vd.vd_name sm.sm_spec_vars with
		  | Some vd -> true
		  | None -> false)
	   | None -> false)
    | _ -> failwith ("Field name " ^ vd.vd_name ^ " has incorrect format\n")

let is_private_var_decl (prog : program) (vd : var_decl) : bool =
  not (is_public_var_decl prog vd)

let mname_of_field (vd : var_decl) : ident =
  match Util.split_by "." vd.vd_name with
    | [mname;_] -> mname
    | _ -> failwith ("Field name " ^ vd.vd_name ^ " has incorrect format\n")

let is_owned_by (prog : program) (owner : ident) (vd : var_decl) : bool =
  match vd.vd_owner with
    | Some id -> id = owner
    | None ->
	match find_im (mname_of_field vd) prog with
	  | Some im -> 
	      (match im.im_owner with
		 | Some id -> id = owner
		 | None -> false)
	  | None -> false

let mk_initial_value
    (prog : program) 
    (impl : impl_module) 
    (fm : (ident, esc_type) Hashtbl.t) 
    (vd : var_decl) : unit =
  let mname = mname_of_field vd in
    if vd.vd_name = arrayStateId then
      Hashtbl.add fm vd.vd_name ArrStET
    else if mname = impl.im_name then
      (** fields of the class being analyzed **)
      let escapes = is_public_var_decl prog vd in
      let ival = initial_value_of_field prog vd escapes in
	(if not (Hashtbl.mem fm vd.vd_name) then
	   Hashtbl.add fm vd.vd_name ival)
    else if is_owned_by prog impl.im_name vd then
      (** owned fields escape if they are static **)
      let escapes = is_static_field vd in
      let ival = initial_value_of_field prog vd escapes in
	(if not (Hashtbl.mem fm vd.vd_name) then
	   Hashtbl.add fm vd.vd_name ival)
    else
      (** all other fields escape **)
      let ival = initial_value_of_field prog vd true in
	(if not (Hashtbl.mem fm vd.vd_name) then
	   Hashtbl.add fm vd.vd_name ival)

(** Result may contain duplicates. **)
let get_called_methods (p : proc_def) : (ident * ident) list =
  let rec get (c : command) : (ident * ident) list =
    match c with
      | Basic {bcell_cmd = bc} ->
	  (match bc with
	     | ProcCall pc -> [(pc.callee_module, pc.callee_name)]
	     | _ -> [])
      | Seq cl 
      | Choice cl 
      | PickAny {pa_body = cl} 
      | PickWitness {pw_body = cl} 
      | Assuming {assuming_body = cl}
      | Induct {induct_body = cl} 
      | Contradict {contradict_body = cl} 
      | Proof {proof_body = cl} -> 
	  List.flatten (List.map get cl)
      | If {if_then = it; if_else = ie} ->
	  (get it) @ (get ie)
      | Loop {loop_prebody = pre; loop_postbody = post} ->
	  (get pre) @ (get post)
      | Return _ -> []
  in
    get p.p_body
      
let is_proc_def 
    (mname : ident) (pname : ident) ((m, p) : m_proc_def) : bool =
  mname = m && pname = p.p_header.p_name 

let collect_methods 
    (prog : program) (impl : impl_module) : m_proc_def list =
  let rec collect 
      (processed : m_proc_def list) 
      (toprocess : (ident * ident) list) : m_proc_def list =
    match toprocess with
      | (mname, pname) :: rest -> 
	  if List.exists (is_proc_def mname pname) processed then
	    collect processed rest
	  else
	    let im = must_find_im mname prog in
	    let pd = must_find_proc pname im in
	    let processed' = processed @ [(mname, pd)] in
	    let toprocess' = rest @ (get_called_methods pd) in
	      collect processed' toprocess'
      | [] -> processed
  in
  let roots = impl.im_procs in
  let callees = List.flatten (List.map get_called_methods roots) in
  let processed = List.map (fun r -> (impl.im_name, r)) roots in
    collect processed callees

let rec fields_of_form (locals : ident list) (f : form) : ident list =
  match f with
    | Var id -> if List.mem id locals then [] else [id]
    | TypedForm(f', _) -> fields_of_form locals f'
    | App(fa, fs) -> 
	(fields_of_form locals fa) @ 
	  (List.flatten (List.map (fields_of_form locals) fs))
    | Const _ -> []
    | Binder(b, til, f') -> 
	let ids, _ = List.split til in
	  fields_of_form (locals @ ids) f'

let get_fields (locals : ident list) (c : command) : ident list =
  let fields_of_form = fields_of_form locals in
  let rec get (c : command) : ident list =
    match c with
      | Basic bc ->
	  (match bc.bcell_cmd with
	     | VarAssign {assign_lhs = lhs; assign_rhs = rhs} ->
		 let lhs_var = if List.mem lhs locals then [] else [lhs] in
		 let rhs_vars = fields_of_form rhs in
		   lhs_var @ rhs_vars
	     | Alloc {alloc_lhs = lhs} ->
		 if List.mem lhs locals then [] else [lhs]
	     | ArrayAlloc {arr_alloc_lhs = lhs; arr_alloc_dims = dims} ->
		 let lhs_var = if List.mem lhs locals then [] else [lhs] in
		 let dims_vars = List.flatten (List.map fields_of_form dims) in
		   lhs_var @ dims_vars
	     | ProcCall {callee_res = reso; callee_args = args} ->
		 let res_var = match reso with
		   | None -> []
		   | Some v -> if List.mem v locals then [] else [v] in
		 let args_vars = List.flatten (List.map fields_of_form args) in
		   res_var @ args_vars
	     | _ -> [])
      | Seq cl 
      | Choice cl 
      | PickAny {pa_body = cl} 
      | PickWitness {pw_body = cl} 
      | Assuming {assuming_body = cl}
      | Induct {induct_body = cl} 
      | Contradict {contradict_body = cl} 
      | Proof {proof_body = cl} -> 
	  List.flatten (List.map get cl)
      | If {if_then = it; if_condition = ic; if_else = ie} ->
	  (get it) @ (fields_of_form ic) @ (get ie)
      | Loop {loop_prebody = pre; loop_test = test; loop_postbody = post} ->
	  (get pre) @ (fields_of_form test) @ (get post)
      | Return {return_exp = fo} -> 
	  (match fo with
	     | None -> []
	     | Some f -> fields_of_form f) 
  in
    get c

let rec is_var (vname : string) (vds : var_decl list) : bool =
  match vds with
    | [] -> false
    | vd::vds' -> vd.vd_name = vname || is_var vname vds'

let collect_fields 
    (prog : program) (methods : m_proc_def list) : var_decl list =
  let rec add_fields
      (processed : var_decl list) (toprocess : ident list) : var_decl list =
    match toprocess with
      | [] -> processed
      | fd :: rest ->
	  if is_var fd processed then
	    add_fields processed rest
	  else 
	    (match vd_of_field prog fd with
	       | Some vd -> add_fields (processed @ [vd]) rest
	       | None -> 
		   if fd = str_rtrancl then
		     add_fields processed rest
		   else if is_oldname fd then
		     add_fields processed ((unoldname fd) :: rest)
		   else
		     failwith ("var_decl for " ^ fd ^ " not found.\n"))
  in
  let handle_method 
      (processed : var_decl list) 
      ((mname, pd) : m_proc_def) : var_decl list =
    add_fields processed (get_fields (get_locals pd) pd.p_body)
  in
    List.fold_left handle_method [] methods

let collect_all_vardefs (prog : program) : specvar_def list =
  let rec add_vardefs
      (processed : specvar_def list) 
      (toprocess : specvar_def list) : specvar_def list =
    match toprocess with
      | [] -> processed
      | (id, f) :: rest -> 
	  if List.mem_assoc id processed then
	    add_vardefs processed rest
	  else 
	    let f' = fst (TypeReconstruct.reconstruct_types [] f) in
	      add_vardefs (processed @ [(id, f')]) rest
  in
  let process_impl 
      (processed : specvar_def list) (impl : impl_module) : specvar_def list =
    add_vardefs (add_vardefs processed impl.im_vardefs) impl.im_constdefs
  in
  let process_spec
      (processed : specvar_def list) (spec : spec_module) : specvar_def list =
    add_vardefs (add_vardefs processed spec.sm_constdefs) spec.sm_vardefs
  in
  let vardefs = List.fold_left process_impl [] prog.p_impls in
    List.fold_left process_spec vardefs prog.p_specs

let collect_all_fields (prog : program) : var_decl list =
  let rec add_fields
      (processed : var_decl list) (toprocess : var_decl list) : var_decl list =
    match toprocess with
      | [] -> processed
      | vd :: rest -> 
	  if is_var vd.vd_name processed then
	    add_fields processed rest
	  else add_fields (processed @ [vd]) rest
  in
  let process_impl 
      (processed : var_decl list) (impl : impl_module) : var_decl list =
    add_fields processed impl.im_vars
  in
  let process_spec
      (processed : var_decl list) (spec : spec_module) : var_decl list =
    add_fields processed spec.sm_spec_vars
  in
  let fields = List.fold_left process_impl [] prog.p_impls in
    List.fold_left process_spec fields prog.p_specs

let initial_value_of_local
    (prog : program) (escapes : bool) (vd : var_decl) : esc_type =
  initial_value_of_type prog vd.vd_basetype escapes vd.vd_type 

let initialize_locals
    (prog : program) 
    (proc : proc_def)
    (ctxt : context) : (ident, esc_type) Hashtbl.t =
  let size = 
    (List.length proc.p_locals) + (List.length proc.p_header.p_formals) in  
  let vm = Hashtbl.create size in
  let initialize_local (escapes : bool) (vd : var_decl) : unit =
    let ival = 
      if vd.vd_name = result_var then unsome ctxt.ret_type
      else initial_value_of_local prog escapes vd in
      Hashtbl.add vm vd.vd_name ival
  in
  let initialize_param (arg_escapes : esc_type) (vd : var_decl) : unit =
    Hashtbl.add vm vd.vd_name arg_escapes
  in
(*  let locals = List.filter is_concrete_vd proc.p_locals in *)
  let locals = proc.p_locals in
  let _ = List.iter (initialize_local false) locals in
  let _ = List.iter2 initialize_param ctxt.arg_types proc.p_header.p_formals in
  let restype = proc.p_header.p_restype in
  let _ = match restype with
    | TypeApp(TypeUnit, []) -> () (** does not return a value **)
    | _ ->
	if not (Hashtbl.mem vm result_var) then
	  Hashtbl.add vm result_var (unsome ctxt.ret_type)
  in
    vm

let print_analysis_state (m : (ident, esc_type) Hashtbl.t) : unit =
  Hashtbl.iter 
    (fun x y -> 
       debug_msg ("** [" ^ x ^ " : " ^ (string_of_esc_type y) ^ "]\n"))
    m;
  debug_msg ("\n")

let state_unchanged 
    (os : (ident, esc_type) Hashtbl.t) 
    (ns : (ident, esc_type) Hashtbl.t) : bool = 
  let get_key (k : ident) (_ : esc_type) (acc : ident list) : ident list =
    acc @ [k]
  in
  let same_mapping (k : ident) : bool =
    (Hashtbl.find os k) = (Hashtbl.find ns k)
  in
    List.for_all same_mapping (Hashtbl.fold get_key os [])

let get_result
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (id : ident) : esc_type =
  let id = if is_oldname id then unoldname id else id in
  let result = 
    try
      Hashtbl.find vm id
    with Not_found ->
      try
	Hashtbl.find fm id
      with Not_found ->
	failwith ("Could not find result for " ^ id ^ "\n")
  in
    debug_msg (id ^ " : " ^ (string_of_esc_type result) ^ "\n");
    result
	
let get_arr_elem_esc_type (e : esc_type) : esc_type =
  match e with
    | ObjET (_, Some e') -> e'
    | _ -> failwith ("Incorrect type for array " ^ 
		       (string_of_esc_type e) ^ "\n")

let get_set_elem_esc_type (e : esc_type) : esc_type =
  match e with
    | SetET e' -> e'
    | _ -> failwith ("Incorrect type for set " ^ 
		       (string_of_esc_type e) ^ "\n")

let min_tval (t1 : tval) (t2 : tval) : tval =
  match t1, t2 with
    | TPublic, _ 
    | _, TPublic -> TPublic
    | TReturned, _
    | _, TReturned -> TReturned
    | _ -> TPrivate

let match_elem_ty (tv : tval) (elem_ty : esc_type) : esc_type =
  match tv with
    | TPublic -> mk_escaped elem_ty
    | TReturned -> mk_returned elem_ty
    | TPrivate -> elem_ty

let rec min_esc_type (e : esc_type) (e' : esc_type) : esc_type =
  debug_msg ("min ("  ^ (string_of_esc_type e) ^ ", " ^ 
	       (string_of_esc_type e') ^ ")\n");
  let result = if e = e' then e
  else
    match e, e' with
      | ObjET (tv1, eto1), ObjET (tv2, eto2) ->
	  let min_tv = min_tval tv1 tv2 in
	  let min_eto = 
	    match eto1, eto2 with
	      | Some et1, Some et2 -> 
		  let min = min_esc_type et1 et2 in
		    Some (match_elem_ty min_tv min)
	      | _ -> None in
	    ObjET (min_tv, min_eto)
      | SetET e1, SetET e2 -> SetET (min_esc_type e1 e2)
      | TupET es, TupET es' -> TupET (List.map2 min_esc_type es es')
      | EmptyET, SetET _
      | NullET, ObjET _ -> e'
      | SetET _, EmptyET
      | ObjET _, NullET -> e
      | FunET (earg1, eres1), FunET (earg2, eres2) ->
	  FunET (min_esc_type earg1 earg2, min_esc_type eres1 eres2)
      | _ -> failwith ("min_esc_type did not expect: " ^ 
			 (string_of_esc_type e) ^ "; " ^ 
			 (string_of_esc_type e') ^ "\n")
  in
    debug_msg ("min ("  ^ (string_of_esc_type e) ^ ", " ^ 
		 (string_of_esc_type e') ^ ") = " ^ 
		 (string_of_esc_type result) ^ "\n");
    result

let max_tval (t1 : tval) (t2 : tval) : tval =
  match t1, t2 with
    | TPrivate, _
    | _, TPrivate -> TPrivate
    | TReturned, _
    | _, TReturned -> TReturned
    | _ -> TPublic

let rec max_esc_type (e : esc_type) (e' : esc_type) : esc_type =
  if e = e' then e
  else
    match e, e' with
      | ObjET (tv1, eto1), ObjET (tv2, eto2) ->
	  let max_tv = max_tval tv1 tv2 in
	  let max_eto =
	    match eto1, eto2 with
	      | Some et1, Some et2 -> 
		  let max = max_esc_type et1 et2 in
		    Some (match_elem_ty max_tv max)
	      | Some et, _
	      | _, Some et -> Some (match_elem_ty max_tv et)
	      | None, None -> None in
	    ObjET (max_tv, max_eto)
      | SetET e1, SetET e2 -> SetET (max_esc_type e1 e2)
      | TupET es, TupET es' -> TupET (List.map2 max_esc_type es es')
      | PrimET, _
      | _, PrimET -> PrimET
      | _ -> failwith ("max_esc_type did not expect: " ^ 
			 (string_of_esc_type e) ^ "; " ^ 
			 (string_of_esc_type e') ^ "\n")

let special_min_esc_type (e1 : esc_type) (e2 : esc_type) : esc_type * esc_type =
  match e1, e2 with
    | ObjET (tv1, Some _), ObjET (tv2, None) ->
	if tv1 = TPublic || tv2 = TPublic then
	  (mk_escaped e1, mk_escaped e2)
	else if tv1 = TReturned || tv2 = TReturned then
	  (mk_returned e1, mk_returned e2)
	else
	  (e1, e2)
    | ObjET (tv1, None), ObjET (tv2, Some et) ->
	let e1' = ObjET (tv1, Some et) in
	  if tv1 = TPublic || tv2 = TPublic then
	    (mk_escaped e1', mk_escaped e2)
	  else if tv1 = TReturned || tv2 = TReturned then
	    (mk_returned e1', mk_returned e2)
	  else
	    (e1', e2)
    | _ -> let e = min_esc_type e1 e2 in (e, e)

let static_min_esc_type (efun : esc_type) (e : esc_type) : esc_type =
  match efun with
    | FunET (earg, eres) -> FunET (earg, (min_esc_type eres e))
    | _ -> failwith ("static_min_esc_type did not expect: " ^ 
		       (string_of_esc_type efun) ^ "; " ^ 
		       (string_of_esc_type e) ^ "\n")

let is_static_field_form
    (prog : program)
    (f : form) : bool =
  match f with
    | Var v
    | TypedForm(Var v, _) ->
	let v = if is_oldname v then unoldname v else v in
	  (match vd_of_field prog v with
	     | None -> false
	     | Some vd -> is_static_field vd)
    | _ -> false

let tval_le (t1 : tval) (t2 : tval) : bool =
  match t1, t2 with
    | TPublic, _
    | TReturned, TReturned
    | TReturned, TPrivate
    | TPrivate, TPrivate -> true
    | _ ->  false

let rec esc_le (et1 : esc_type) (et2 : esc_type) : bool =
  match et1, et2 with
    | PrimET, PrimET -> true
    | ObjET (tv1, eto1), ObjET (tv2, eto2) ->
	(tval_le tv1 tv2) &&
	  (match eto1, eto2 with
	     | Some et1, Some et2 -> esc_le et1 et2
	     | Some et, _ -> false
	     | _ -> true)
    | SetET et1, SetET et2 ->
	esc_le et1 et2
    | TupET ets1, TupET ets2 ->
	List.for_all2 esc_le ets1 ets2
    | FunET (et1, et2), FunET (et3, et4) ->
	esc_le et1 et3 && esc_le et2 et4
    | _ -> failwith (" esc_le did not expect: " ^ (string_of_esc_type et1) ^
		       ", " ^ (string_of_esc_type et2) ^ "\n")
	

let rec apply_lambda_type (eargs : esc_type list) (et : esc_type) : esc_type =
  match eargs with
    | [] -> et
    | et1::es ->
	(match et with
	   | FunET (earg, eres) ->
	       if esc_le earg et1 then
		 apply_lambda_type es eres
	       else
		 apply_lambda_type es (mk_escaped eres)
	   | _ -> failwith ("apply_lambda_type failed on: " ^ 
			      (string_of_esc_type et) ^ "\n"))

let rec unapply_lambda_type (eargs : esc_type list) (et : esc_type) : esc_type =
  match eargs with
    | [] -> et
    | e1::es -> FunET(e1, unapply_lambda_type es et)

let mk_rename_map
    (prog : program)
    (fm : (ident, esc_type) Hashtbl.t)
    (vm : (ident, esc_type) Hashtbl.t)
    (escaped : bool)
    (til : typedIdent list) : substMap * ident list * esc_type list =
  let rec mk_fresh (id : ident) : ident =
    if Hashtbl.mem fm id || Hashtbl.mem vm id then
      Util.fresh_name id
    else id
  in
  let rec mk_map 
      (map : substMap) 
      (processed : ident list)
      (es : esc_type list)
      (toprocess : typedIdent list) : substMap * ident list * esc_type list =
    match toprocess with
      | (id, tf) :: rest ->
	  let new_id = mk_fresh id in
	  let new_map = if id = new_id then map
	  else map @ [(id, Var new_id)] in
	  let et = initial_value_of_type prog None escaped tf in
	    Hashtbl.add vm new_id et;
	    mk_map new_map (processed @ [new_id]) (es @ [et]) rest
      | [] -> (map, processed, es)
  in
    mk_map [] [] [] til

let set_field_result
    (fm : (ident, esc_type) Hashtbl.t) 
    (id : ident) 
    (e : esc_type) : unit =
  if Hashtbl.mem fm id then
    Hashtbl.replace fm id e
  else failwith ("Could not find field mapping for " ^ id ^ "\n")

let rec remove_returned (e : esc_type) : esc_type =
  match e with
    | ObjET (tv, eto) ->
	let tv' = if tv = TReturned then TPublic else tv in
	  (match eto with
	     | Some et -> ObjET (tv', Some (remove_returned et))
	     | None -> ObjET (tv', None))
    | SetET et ->
	SetET (remove_returned et)
    | TupET ets ->
	TupET (List.map remove_returned ets)
    | FunET (et1, et2) ->
	FunET (remove_returned et1, remove_returned et2)
    | _ -> e

let set_result
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (id : ident) 
    (e : esc_type) : unit =
  let id = if is_oldname id then unoldname id else id in
    if Hashtbl.mem vm id then
      let _ = debug_msg (id ^ " := " ^ (string_of_esc_type e) ^ "\n") in
	Hashtbl.replace vm id e
    else if Hashtbl.mem fm id then
      let e' = remove_returned e in
      let _ = debug_msg (id ^ " := " ^ (string_of_esc_type e') ^ "\n") in
	Hashtbl.replace fm id e'
    else failwith ("Could not find mapping for " ^ id ^ "\n")

let result_of_form
    (prog : program)
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (f : form) : esc_type =
  let rec result_of_form  
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (f : form) : esc_type =
    let result = match f with
      | Const NullConst -> NullET
      | Const EmptysetConst -> EmptyET
      | Const (IntConst _) 
      | Const (BoolConst _) -> PrimET
      | Var id -> get_result fm vm id
      | App(Const FieldRead, [ffld; fobj]) ->
	  let efld = result_of_form fm vm ffld in
	  let eobj = result_of_form fm vm fobj in
	  let efld = 
	    if is_static_field_form prog ffld then
	      apply_lambda_type [eobj] efld 
	    else 
	      efld 
	  in
	    (match eobj with
	       | ObjET (tv, eto) ->
		   if tv = TPublic || tv = TReturned then
		     mk_escaped efld
		   else efld
	       | _ ->
		   failwith ("Unexpected result " ^ (string_of_esc_type eobj) ^ 
			       " for " ^ (PrintForm.string_of_form fobj) ^ "\n"))
      | App(Const FieldWrite, [ffld; fobj; frhs]) ->
	  let efld = result_of_form fm vm ffld in
	  let eobj = result_of_form fm vm fobj in
	  let erhs = result_of_form fm vm frhs in
	    (match eobj with
	       | ObjET (tv, eto) ->
		   if tv = TPublic || tv = TReturned then
		     mk_escaped efld
		   else if is_static_field_form prog ffld then
		     static_min_esc_type efld erhs
		   else
		     min_esc_type efld erhs
	       | _ ->
		   failwith ("Unexpected result " ^ (string_of_esc_type eobj) ^ 
			       " for " ^ (PrintForm.string_of_form fobj) ^ "\n"))
      | App(Const ArrayRead, [arrStf; arrf; indf]) ->
	  let earr = result_of_form fm vm arrf in
	  let eelm = get_arr_elem_esc_type earr in
	    (match earr with	     
	       | ObjET (tv, _) ->
		   if tv = TPublic || tv = TReturned then
		     mk_escaped eelm
		   else eelm
	       | _ ->
		   failwith ("Unexpected result " ^ (string_of_esc_type earr) ^ 
			       " for " ^ (PrintForm.string_of_form arrf) ^ "\n"))
      | App(Const ArrayWrite, [arrStf; _; _; _]) ->
	  result_of_form fm vm arrStf
      | App(Const Ite, [_; f1; f2])
      | App(Const Cup, [f1; f2]) ->
	  let ef1 = result_of_form fm vm f1 in
	  let ef2 = result_of_form fm vm f2 in
	    min_esc_type ef1 ef2
      | App(Const FiniteSetConst, [f']) -> SetET (result_of_form fm vm f')
      | App(Const Tuple, fs) -> TupET (List.map (result_of_form fm vm) fs)
      | App(Const Minus, [f'; _]) (** sometimes minus gets confused with diff *)
      | App(Const Diff, [f'; _])
      | App(Const UMinus, [f'])
      | TypedForm(f', _) -> result_of_form fm vm f'
      | App(Const Not, _)
      | App(Const And, _)
      | App(Const Eq, _)
      | App(Const Lt, _)
      | App(Const LtEq, _)
      | App(Const Gt, _)
      | App(Const GtEq, _)
      | App(Const Plus, _)
      | App(Const Mult, _)
      | App(Const Div, _)
      | App(Const Mod, _) 
      | App(TypedForm(Var "rtrancl_pt", _), _) -> PrimET
      | App(fapp, fs) ->
	  let eapp = result_of_form fm vm fapp in
	  let efs = List.map (result_of_form fm vm) fs in
	    apply_lambda_type efs eapp
      | Binder (Comprehension, [(v, tf)], f') ->
	  let fm' = Hashtbl.copy fm in
	  let vm' = Hashtbl.copy vm in
	  let et = initial_value_of_type prog None true tf in
	    if Hashtbl.mem vm' v then
	      Hashtbl.remove vm' v
	    else if Hashtbl.mem fm' v then
	      Hashtbl.remove fm' v;
	    Hashtbl.add vm' v et;
	    constrain_form fm' vm' f';
	    SetET (Hashtbl.find vm' v)
      | Binder (Lambda, til, f') ->
	  let rm, vs, es = mk_rename_map prog fm vm false til in
	  let frenamed = subst rm f' in
	  let result = result_of_form fm vm frenamed in
	    List.iter (Hashtbl.remove vm) vs;
	    unapply_lambda_type es result
      | _ -> failwith ("Unexpected form in result_of_form: " ^ 
			 (MlPrintForm.string_of_form f) ^ "\n")
    in
      result
	
  and constrain_form
      (fm : (ident, esc_type) Hashtbl.t) 
      (vm : (ident, esc_type) Hashtbl.t) 
      (f : form) : unit =
    debug_msg ("constraint: " ^ (PrintForm.string_of_form f) ^ "\n");
    match f with
      | App(Const Not, _)
      | App(Const Lt, _)
      | App(Const LtEq, _) -> ()
      | App(Const Eq, [f1; f2]) ->
	  let ef1 = result_of_form fm vm f1 in
	  let ef2 = result_of_form fm vm f2 in
	  let max = max_esc_type ef1 ef2 in
	    add_constraint fm vm f1 max;
	    add_constraint fm vm f2 max
      | App(Const Or, fs) ->
	  let rec handle_disjunct 
	      (f : form) : 
	      (ident, esc_type) Hashtbl.t * (ident, esc_type) Hashtbl.t =
	    let fm' = Hashtbl.copy fm in
	    let vm' = Hashtbl.copy vm in
	    let _ = constrain_form fm' vm' f in
	      (fm', vm')
	  in
	  let reconcile 
	      (fms : (ident, esc_type) Hashtbl.t list)
	      (vms : (ident, esc_type) Hashtbl.t list)
	      (id : ident)
	      (_ : esc_type) : unit =
	    let ets = List.map2 (fun x y -> get_result x y id) fms vms in
	    let et = match ets with
	      | [x] -> x
	      | x::rest -> List.fold_left min_esc_type x rest
	      | _ -> failwith ("empty or in constrain form.\n") in
	      set_result fm vm id et
	  in
	  let fms, vms = List.split (List.map handle_disjunct fs) in
	    Hashtbl.iter (reconcile fms vms) fm;
	    Hashtbl.iter (reconcile fms vms) vm
      | App(Const And, fs) ->
	  List.iter (constrain_form fm vm) fs
      | App(TypedForm(Var "rtrancl_pt", _), 
	    [Binder(Lambda, [(x, _); (y, _)], f'); froot; farg]) ->
	  let eroot = result_of_form fm vm froot in
	  let fsubst = subst [(x, froot); (y, farg)] f' in
	  let fm' = Hashtbl.copy fm in
	  let vm' = Hashtbl.copy vm in
	  let _ = constrain_form fm' vm' fsubst in
	  let earg = result_of_form fm' vm' farg in
	  let min = min_esc_type eroot earg in
	    add_constraint fm vm farg min
      | App(Const Elem, [felem; fset]) ->
	  let eelem = result_of_form fm vm felem in
	  let eset = result_of_form fm vm fset in
	  let max = max_esc_type eelem (get_set_elem_esc_type eset) in
	    add_constraint fm vm felem max;
	    add_constraint fm vm fset (SetET max)
      | Binder(Exists, til, f') ->
	  let rm, vs, _ = mk_rename_map prog fm vm true til in
	  let frenamed = subst rm f' in
	  let _ = constrain_form fm vm frenamed in
	    List.iter (Hashtbl.remove vm) vs
      | _ -> failwith ("constrain_form did not expect: " ^ 
			 (MlPrintForm.string_of_form f) ^ "\n")
	  
  and add_constraint
      (fm : (ident, esc_type) Hashtbl.t) 
      (vm : (ident, esc_type) Hashtbl.t) 
      (f : form) 
      (et : esc_type) : unit =
    debug_msg ("constrain: " ^ (PrintForm.string_of_form f) ^ " --> " ^ (string_of_esc_type et) ^ "\n");
    match f with
      | Var v -> set_result fm vm v et
      | App(Const FieldRead, [ffld; fobj]) ->
	  let eobj = result_of_form fm vm fobj in
	  let efld = if is_static_field_form prog ffld 
	  then unapply_lambda_type [eobj] et else et in
	    (match et with
	       | ObjET (tv, _) ->
		   if tv = TPrivate then
		     add_constraint fm vm fobj 
		       (mk_unescaped eobj)
	       | PrimET 
	       | SetET _ -> ()
	       | _ ->
		   failwith ("add_constraint did not expect constraint " ^
			       (string_of_esc_type et) ^ "\n"));
	    add_constraint fm vm ffld efld
      | App(Const ArrayRead, [_; arrf; _]) ->
	  let earr = result_of_form fm vm arrf in
	    (match et with
	       | ObjET (tv, _) ->
		   if tv = TPrivate then
		     add_constraint fm vm arrf
		       (mk_unescaped_arr_and_elem earr)
	       | PrimET -> ()
	       | _ ->
		   failwith ("add_constraint did not expect constraint " ^
			       (string_of_esc_type et) ^ "\n"))
      | TypedForm(f', _) -> add_constraint fm vm f' et
      | _ -> failwith ("add_constraint did not expect: " ^ 
			 (PrintForm.string_of_form f) ^ "\n")

  in
  let result = result_of_form fm vm f in
    debug_msg ((PrintForm.string_of_form f) ^ " : " ^ (string_of_esc_type result) ^ "\n");
    result
      
let mk_arr_result
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (old_e : esc_type) 
    (new_elem_e : esc_type) : esc_type =
  match old_e with
    | ObjET (tv, Some _) -> ObjET (tv, Some new_elem_e)
    | _ -> failwith ("Incorrect type for array " ^ 
		       (string_of_esc_type old_e) ^ "\n")

(*
let set_arr_result
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (id : ident) 
    (old_e : esc_type) 
    (new_elem_e : esc_type) : unit =
  match old_e with
    | ObjET (tv, Some _) -> set_result fm vm id (ObjET (tv, Some new_elem_e))
    | _ -> failwith ("Incorrect type for array " ^ 
		       (string_of_esc_type old_e) ^ "\n")
*)

let update_result_of_form
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (f : form)
    (e : esc_type) : unit =
  match f with
    | Var id -> 
	let old_e = get_result fm vm id in
	let min = min_esc_type old_e e in
	  set_result fm vm id min
    | _ -> failwith ("Unexpected form in update_result_of_form: " ^ 
		       (PrintForm.string_of_form f) ^ "\n")

let check_arrSt_id (id : ident) : unit =
  if not (id = arrayStateId) then
    failwith ("Incorrect ident for arrayState " ^ id ^ "\n")

let not_arrSt (vd : var_decl) : bool =
  not (vd.vd_name = arrayStateId)

let rec check_arrSt (f : form) : unit =
  match f with
    | TypedForm(f', _) -> check_arrSt f'
    | Var id -> check_arrSt_id id
    | _ -> failwith ("Incorrect form for arrayState " ^ 
		       (PrintForm.string_of_form f) ^ "\n")

let rec check_var_or_const (f : form) : unit =
  match f with
    | TypedForm(f', _) -> check_var_or_const f'
    | Var _ 
    | Const _ -> ()
    | _ -> 
	failwith ("Not a Var or Const " ^ (PrintForm.string_of_form f) ^ "\n")

let check_prim_id 
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (id : ident) : unit =
  let r = get_result fm vm id in
    match r with
      | PrimET -> ()
      | _  ->
	  failwith ("check_prim_id failed on " ^ 
		      (string_of_esc_type r) ^ " for " ^ id ^ "\n")
(*
let check_arr_id 
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (id : ident) : unit =
  let r = get_result fm vm id in
    match r with
      | ArrET _ -> ()
      | _  ->
	  failwith ("check_arr_id failed on " ^ 
		      (string_of_esc_type r) ^ " for " ^ id ^ "\n")

let check_obj_or_arr_id 
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (id : ident) : unit =
  let r = get_result fm vm id in
    match r with
      | ObjET _ -> ()
      | _  ->
	  failwith ("check_obj_or_arr_id failed on " ^ 
		      (string_of_esc_type r) ^ " for " ^ id ^ "\n")
*)

let check_set_id 
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (id : ident) : unit =
  let r = get_result fm vm id in
    match r with
      | SetET _ -> ()
      | _  ->
	  failwith ("check_set_id failed on " ^ 
		      (string_of_esc_type r) ^ " for " ^ id ^ "\n")

let rec check_prim_form 
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (f : form) : unit =
  match f with
    | Const  _ -> ()
    | Var id -> check_prim_id fm vm id
    | TypedForm(f', _) -> check_prim_form fm vm f'
    | _ -> failwith ("Failed integer check: " ^ 
		       (PrintForm.string_of_form f) ^ "\n")

let result_of_var_decl 
    (vm : (ident, esc_type) Hashtbl.t) (vd : var_decl) : esc_type =
  Hashtbl.find vm vd.vd_name 

let is_prim_op (c : constValue) : bool =
  match c with
    | Plus | Minus | Mult | Div | Mod | Lt | Gt | LtEq | GtEq -> true
    | _ -> false

(*
let not_escaped_arr_id
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (id : ident) : bool =
  match get_result fm vm id with
    | ArrET (b, _) -> not b
    | _ -> false
	
let not_escaped_obj_id
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (id : ident) : bool =
  match get_result fm vm id with
    | ObjET b -> not b
    | _ -> false
*)

let writeable_arr
    (prog : program)
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (f : form) : bool =
  let result = match result_of_form prog fm vm f with
    | ObjET (TPrivate, _)
    | ObjET (TReturned, _) -> true
    | _ -> false
  in
  let msg = if result then "ok " else "not ok " in
    debug_msg ((PrintForm.string_of_form f) ^ " is " ^ msg ^ "to write.\n");
    result
	
let writeable_obj
    (prog : program)
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (f : form) : bool =
  let result = match result_of_form prog fm vm f with
    | ObjET (TPrivate, _) 
    | ObjET (TReturned, _) -> true
    | _ -> false
  in
  let msg = if result then "ok " else "not ok " in
    debug_msg ((PrintForm.string_of_form f) ^ " is " ^ msg ^ "to write.\n");
    result

let ok_to_write
    (prog : program)
    (cm : impl_module) (** impl_module of candidate class **)
    (vm : (ident, esc_type) Hashtbl.t) 
    (id : ident) : bool =
  let result =
    (** some special variables are okay to write **)
    id = arrayStateId || id = "Object.alloc" ||
    (** as are local variables **)
    Hashtbl.mem vm id ||
    (** static fields must be private or abstract and 
	in the class we are checking **)
    (match vd_of_field prog id with
       | None -> failwith ("Could not find var_decl for " ^ id)
       | Some vd ->
	   if is_static_field vd then
	     (mname_of_field vd = cm.im_name && 
		 (vd.vd_abstract || is_private_var_decl prog vd))
	   else true)
  in
  let msg = if result then "ok " else "not ok " in
    debug_msg (id ^ " is " ^ msg ^ "to write.\n");
    result

let rec set_form_result
    (prog : program)
    (fm : (ident, esc_type) Hashtbl.t)
    (vm : (ident, esc_type) Hashtbl.t)
    (f : form)
    (et : esc_type) : bool =
  let _ = debug_msg ((PrintForm.string_of_form f) ^ 
		       " := " ^ (string_of_esc_type et) ^ "\n") in
  let set_form_result = set_form_result prog in
  let result_of_form = result_of_form prog in
    match f with
      | Const _ -> true
      | Var id -> set_result fm vm id et; true
      | App(Const FieldRead, [ffld; fobj]) ->
	  let eobj = result_of_form fm vm fobj in
	  let efld = if is_static_field_form prog ffld 
	  then unapply_lambda_type [eobj] et else et in
	    set_form_result fm vm ffld efld
      | App(Const FieldWrite, [ffld; fobj; frhs]) ->
	  let eobj = result_of_form fm vm fobj in
	  let erhs = if is_static_field_form prog ffld 
	  then apply_lambda_type [eobj] et else et in
	    set_form_result fm vm ffld et &&
	    set_form_result fm vm frhs erhs &&
	    writeable_obj prog fm vm fobj
      | App(Const ArrayRead, [arrStf; arrf; indf]) ->
	  let earr = result_of_form fm vm arrf in
	  let arr_min = mk_arr_result fm vm earr et in
	    check_arrSt arrStf;
	    set_form_result fm vm indf PrimET &&
	      set_form_result fm vm arrf arr_min
      | App(Const ArrayWrite, [arrStf; arrf; indf; rhsf]) ->
	  let earr = result_of_form fm vm arrf in
	  let eelem = get_arr_elem_esc_type earr in
	  let erhs = result_of_form fm vm rhsf in
	  let min = min_esc_type erhs eelem in
	  let arr_min = mk_arr_result fm vm earr min in
	    set_form_result fm vm arrStf et &&
	      set_form_result fm vm arrf arr_min &&
	      set_form_result fm vm indf PrimET &&
	      set_form_result fm vm rhsf min &&
	      writeable_arr prog fm vm arrf
      | App(Const FiniteSetConst, [f']) ->
	  let eelm = get_set_elem_esc_type et in
	    set_form_result fm vm f' eelm
      | App(Const Plus, [f1; f2])
      | App(Const Minus, [f1; f2])
      | App(Const Mult, [f1; f2])
      | App(Const Div, [f1; f2])
      | App(Const Mod, [f1; f2])
      | App(Const Diff, [f1; f2])
      | App(Const Cup, [f1; f2]) ->
	  set_form_result fm vm f1 et &&
	    set_form_result fm vm f2 et
      | App(Const Tuple, fs) ->
	  (match et with
	     | TupET ets -> List.for_all2 (set_form_result fm vm) fs ets
	     | _ -> failwith ("Expected tuple type, got " ^ 
				(string_of_esc_type et) ^ "\n"))
      | App(Const Lt, _) (** Queries do not add additional constraints. **)
      | App(Const LtEq, _)
      | App(Const Gt, _)
      | App(Const GtEq, _)
      | App(Const Eq, _)
      | App(Const Or, _)
      | App(Const And, _) 
      | App(Const Not, _)
      | Binder(Comprehension, _, _) -> true
      | App(Const Ite, [_; f2; f3]) ->
	  set_form_result fm vm f2 et &&
	    set_form_result fm vm f2 et
      | App(Const UMinus, [f'])
      | TypedForm(f', _) -> set_form_result fm vm f' et
      | App(fapp, fs) ->
	  let efs = List.map (result_of_form fm vm) fs in
	  let eapp = unapply_lambda_type efs et in
	    set_form_result fm vm fapp eapp
      | Binder(Lambda, til, f') ->
	  let rm, vs, es = mk_rename_map prog fm vm false til in
	  let frenamed = subst rm f' in
	  let et' = apply_lambda_type es et in
	  let result = set_form_result fm vm frenamed et' in
	    List.iter (Hashtbl.remove vm) vs;
	    result
      | _ -> 
	  failwith ("Unexpected form in set_form_result: " ^ 
		      (MlPrintForm.string_of_form f) ^ "\n")

let is_hidden_set (prog : program) (id : ident) : bool =
  match Util.split_by "." id with
    | [cname; fname] ->
	is_valid_class prog cname && fname = Jast.hidden_set_name
    | _ -> false

let handle_hidden_update 
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (ac : assign_command) : bool =
  let id = ac.assign_lhs in
    match ac.assign_rhs with
      | App(Const Cup, 
	    [TypedForm(Var set_id, _);
	     App(Const FiniteSetConst, [TypedForm(Var elem_id, _)])])
	  when id = set_id ->
	  let elhs = get_set_elem_esc_type (get_result fm vm id) in
	  let eelem = get_result fm vm elem_id in
	  let min_lhs, min_elem = special_min_esc_type elhs eelem in
	    set_result fm vm id (SetET min_lhs);
	    set_result fm vm elem_id min_elem;
	    true
    | _ -> 
	failwith ("Unexpected rhs in handle_hidden_update: " ^
		    (PrintAst.pr_var_assign ac))
let analyze_assign
    (prog : program)
    (cm : impl_module) (** impl_module of candidate class **)
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (ac : assign_command) : bool =
  let id = ac.assign_lhs in
  let lhs_result = ok_to_write prog cm vm id in
  let _ = if not lhs_result then 
    debug_msg ("Not ok to write lhs of " ^ (PrintAst.pr_var_assign ac) ^ "\n") in
    if is_hidden_set prog id then
      handle_hidden_update fm vm ac
    else
      let elhs = get_result fm vm id in
      let rhs = fst (TypeReconstruct.reconstruct_types [] ac.assign_rhs) in
      let erhs = result_of_form prog fm vm rhs in
      let min = min_esc_type elhs erhs in
      let _ = set_result fm vm id min in
      let rhs_result = set_form_result prog fm vm rhs min in
      let result = lhs_result && rhs_result in
      let msg = if result then "PASSED" else "FAILED" in
	debug_msg ("\n" ^ msg ^ ".\n\n");
	result
      
let mk_full_name (mname : ident) (proc : proc_def) : ident =
  mname ^ "." ^ proc.p_header.p_name

let full_name_of_work (w : work) : ident =
  mk_full_name w.w_mname w.w_method

let string_of_context (ctxt : context) : string =
  "(" ^ (String.concat " -> " (List.map string_of_esc_type ctxt.arg_types)) ^ 
    (match ctxt.ret_type with 
       | None -> " -> ()"
       | Some et -> " -> " ^ (string_of_esc_type et)) ^ ")"

let string_of_work (w : work) : string =
  "Work: " ^ w.w_mname ^ "." ^ w.w_method.p_header.p_name ^ 
    " [" ^ (string_of_context w.w_context) ^ "]"

let string_of_work_list (wl : work list) : string =
  "Work list:\n" ^ (String.concat "\n" (List.map string_of_work wl)) ^ "\n\n"

let print_cache (cache : m_cache) : unit =
  let string_of_summary ((ctxt, result) : m_summary) : string =
    (string_of_context ctxt) ^ " -> " ^
      (match result with
	 | Succeed ctxt' -> "Succeeded " ^ (string_of_context ctxt')
	 | Fail -> "Failed ") in
  let print_entry (id : ident) (summaries : m_summary list) : unit =
    debug_msg ("Results for " ^ id ^ ":\n" ^ 
      (String.concat "\n" (List.map string_of_summary summaries)) ^ "\n") in
    Hashtbl.iter print_entry cache;
    debug_msg "\n"

let analyze_proc_call 
    (prog : program)
    (cm : impl_module) (** impl_module of candidate class **)
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (cache : m_cache)
    (wlr : work list ref)
    (pc : proc_call) : bool =
  let mname = pc.callee_module in
  let im = must_find_im mname prog in
  let pd = must_find_proc pc.callee_name im in
  let full_callee_name = mk_full_name mname pd in
  let results = try Hashtbl.find cache full_callee_name with Not_found -> [] in
  let res_escapes, write_ok = match pc.callee_res with
    | None -> None, true
    | Some id -> Some (Hashtbl.find vm id), ok_to_write prog cm vm id in
  let args_escape = List.map (result_of_form prog fm vm) pc.callee_args in
  let ctxt = { ret_type = res_escapes; arg_types = args_escape; } in
  let result = 
    try 
      let result = List.assoc ctxt results in
	match result with
	  | Fail -> false
	  | Succeed ctxt' ->
	      if not (ctxt = ctxt') then
		(let _ = match pc.callee_res with
		   | None -> ()
		   | Some id -> 
		       let rmin = min_esc_type 
			 (unsome res_escapes) (unsome ctxt'.ret_type) in
			 set_result fm vm id rmin in
		   List.iter2 (update_result_of_form fm vm) 
		     pc.callee_args ctxt'.arg_types);
	      write_ok
    with Not_found -> 
      let new_work = {w_mname = mname; w_method = pd; w_context = ctxt;} in
	wlr := Util.set_add new_work !wlr;
	write_ok
  in
  let msg = if result then "PASSED" else "FAILED" in
    debug_msg ((PrintAst.pr_call pc) ^ " " ^ msg ^ ".\n\n");
    result


let rec analyze_command
    (prog : program)
    (cm : impl_module) (** impl_module of candidate class **)
    (fm : (ident, esc_type) Hashtbl.t) 
    (vm : (ident, esc_type) Hashtbl.t) 
    (cache : m_cache)
    (wlr : work list ref)
    (c : command) : bool =
  let analyze = analyze_command prog cm fm vm cache wlr in
  let result = match c with
    | Basic {bcell_cmd = bc} ->
	debug_msg ("Analyzing [1]: " ^ (PrintAst.pr_basic_cmd bc) ^ "\n");
	(match bc with
	   | Skip 
	   | Assume _
	   | Assert _ 
	   | NoteThat _ 
	   | Havoc _ -> true
	   | Alloc { alloc_lhs = id } 
	   | ArrayAlloc { arr_alloc_lhs = id} -> ok_to_write prog cm vm id
	   | VarAssign ac -> analyze_assign prog cm fm vm ac
	   | ProcCall pc -> analyze_proc_call prog cm fm vm cache wlr pc
 	   | _ -> failwith ("Unrecognized basic command " ^ 
			      (PrintAst.pr_command c) ^ "\n"));
    | Seq cl
    | Choice cl
    | PickAny {pa_body = cl}
    | PickWitness {pw_body = cl}
    | Assuming {assuming_body = cl} 
    | Induct {induct_body = cl} 
    | Proof {proof_body = cl} -> List.for_all analyze cl
    | If {if_condition = cond; if_then = c1; if_else = c2} 
    | Loop {loop_prebody = c1; loop_test = cond; loop_postbody = c2} ->
	debug_msg ("Analyzing loop.\n");
	(match cond with
	   | Const (BoolConst _)
	   | TypedForm(Var _, _) -> analyze c1 && analyze c2
	   | _ -> failwith ("Unrecognized form for condition: " ^
			      (MlPrintForm.string_of_form cond) ^ "\n"))
    | Return {return_exp = fo} ->
	debug_msg ("Analyzing [2]: " ^ (PrintAst.pr_command c));
	let _ = match fo with
	  | None 
	  | Some (Const _) -> ()
	  | Some (TypedForm(Var id, _)) -> 
	      let e1 = get_result fm vm id in
	      let e2 = get_result fm vm result_var in
	      let min = min_esc_type e1 e2 in
		set_result fm vm id min;
		set_result fm vm result_var min
	  | Some f -> 
	      failwith ("Unexpected return value " ^ 
			  (PrintForm.string_of_form f) ^ "\n") in
	  true
    | _ -> failwith ("Unrecognized command " ^ (PrintAst.pr_command c) ^ "\n")
  in
    debug_msg "\n";
    result
	  
let mk_work (mname : ident) (proc : proc_def) (ctxt : context) : work =
  { w_mname = mname; w_method = proc; w_context = ctxt; }

let work_of_dep (cache : m_cache) ((mname, proc) : m_proc_def) : work list =
  let full_proc_name = mk_full_name mname proc in
  let summaries = try Hashtbl.find cache full_proc_name with Not_found -> [] in
  let contexts, _ = List.split summaries in
    List.map (mk_work mname proc) contexts

let rec analyze_method
    (prog : program) 
    (cm : impl_module) (** impl_module of candidate class **)
    (cg : call_graph)
    (fm : (ident, esc_type) Hashtbl.t) 
    (cache : m_cache)
    (w : work) : work list =
  let proc = w.w_method in
  let phdr = proc.p_header in
  let ctxt = w.w_context in
  let vm = initialize_locals prog proc ctxt in
  let _ = print_string ("\nAnalyzing method " ^ phdr.p_name ^ "...\n") in
  let _ = debug_msg ("Initialized local variable map:\n") in
  let _ = print_analysis_state vm in
  let wlr = ref [] in
  let rec analyze () : bool * work list =
    let _ = debug_msg ("Entering analyze...\n") in
    let old_fm = Hashtbl.copy fm in
    let old_vm = Hashtbl.copy vm in
    let _ = print_analysis_state fm in
    let _ = print_analysis_state vm in
    let succeeded = analyze_command prog cm fm vm cache wlr proc.p_body in
      if state_unchanged old_fm fm && state_unchanged old_vm vm then
	(succeeded, !wlr)
      else
	analyze ()
  in    
  let succeeded, new_work = analyze () in
  let full_proc_name = full_name_of_work w in
  let results = try Hashtbl.find cache full_proc_name with Not_found -> [] in
  let new_result =
    if succeeded then
      let res_escapes = match phdr.p_restype with
	| TypeApp(TypeUnit, []) -> None
	| _ -> Some (Hashtbl.find vm result_var) in
      let args_escape = 
	List.map (result_of_var_decl vm) phdr.p_formals in
      let ctxt' = { ret_type = res_escapes; arg_types = args_escape; } in
	Succeed ctxt'
    else Fail
  in
  let results_changed = 
    try
      let old_result = List.assoc ctxt results in
	not (new_result = old_result)
    with Not_found -> true in
    if results_changed then
      let new_results = (List.remove_assoc ctxt results) @ [(ctxt, new_result)] in
      let _ = Hashtbl.replace cache full_proc_name new_results in
      let deps = try Hashtbl.find cg full_proc_name with Not_found -> [] in
      let dep_work = List.flatten (List.map (work_of_dep cache) deps) in
	debug_msg ("Final field map for method " ^ phdr.p_name ^ ":\n");
	print_analysis_state fm;
	debug_msg ("Final local variable map:\n");
	print_analysis_state vm;
	Util.union new_work dep_work
    else
      (debug_msg ("Final field map for method " ^ phdr.p_name ^ ":\n");
       print_analysis_state fm;
       debug_msg ("Final local variable map:\n");
       print_analysis_state vm;
       new_work)

let mk_public_context (prog : program) ((_, proc) : m_proc_def) : context =
  let phdr = proc.p_header in
  let res_type = phdr.p_restype in
  let ret_escapes = match res_type with
    | TypeApp(TypeUnit, []) -> None
    | _ -> Some (initial_value_of_type1 prog phdr.p_basetype TReturned res_type)
  in
  let args_escape = 
    List.map (initial_value_of_local prog true) proc.p_header.p_formals in
    { ret_type = ret_escapes; arg_types = args_escape; }

let is_public_method (pd : proc_def) : bool =
  pd.p_header.p_public

let mk_public_work (prog : program) (mname : ident) (proc : proc_def) : work =
  let cntxt = mk_public_context prog (mname, proc) in
    { w_mname = mname; w_method = proc; w_context = cntxt; }

(** Build a call graph starting from the public methods of the module **)
let build_call_graph (prog : program) (impl : impl_module) : call_graph =
  let cg = Hashtbl.create (List.length impl.im_procs) in
  let add_to_call_graph 
      (caller : m_proc_def) ((mname, pname) : ident * ident) : unit =
    let callee = mname ^ "." ^ pname in
    let callers = try Hashtbl.find cg callee with Not_found -> [] in
      Hashtbl.replace cg callee (Util.set_add caller callers)
  in
  let rec collect 
      (processed : m_proc_def list) (toprocess : (ident * ident) list) : unit =
    match toprocess with
      | [] -> ()
      | (mname, pname) :: rest ->
	  if List.exists (is_proc_def mname pname) processed then
	    collect processed rest
	  else
	    let im = must_find_im mname prog in
	    let pd = must_find_proc pname im in
	    let callees = get_called_methods pd in
	    let _ = List.iter (add_to_call_graph (mname, pd)) callees in
	    let processed' = processed @ [(mname, pd)] in
	    let toprocess' = rest @ (get_called_methods pd) in
	      collect processed' toprocess'
  in
  let public_methods = List.filter is_public_method impl.im_procs in
  let roots = List.map 
    (fun proc -> (impl.im_name, proc.p_header.p_name)) public_methods in
    collect [] roots;
    cg

(** Create a work list consisting of the public methods of the module **)
let mk_work_list (prog : program) (impl : impl_module) : work list =
  let public_methods = List.filter is_public_method impl.im_procs in
    List.map (mk_public_work prog impl.im_name) public_methods

(** Returns true for methods that do not have a 'Fail' result **)
let not_unsuccessful_methods (cache : m_cache) (w : work) : bool =
  let mname = w.w_mname ^ "." ^ w.w_method.p_header.p_name in
    try 
      let ctxts, results = List.split (Hashtbl.find cache mname) in
	not (List.mem Fail results)
    with Not_found -> true

(** Returns true for methods that have a 'Succeed' result **)
let successful_methods (cache : m_cache) (w : work) : bool =
  let mname = w.w_mname ^ "." ^ w.w_method.p_header.p_name in
    try 
      let ctxts, results = List.split (Hashtbl.find cache mname) in
	not (List.mem Fail results)
    with Not_found -> false

let mname_of_work (w : work) : ident =
  w.w_mname ^ "." ^ w.w_method.p_header.p_name

let handle_dependent_var
    (prog : program)
    (cm : impl_module)
    (fm : (ident, esc_type) Hashtbl.t)
    ((id, f) : specvar_def) : unit =
  debug_msg ("\n" ^ id ^ " == " ^ (PrintForm.string_of_form f) ^ "\n");
  let vm = Hashtbl.create 1 in
  let f' = match vd_of_field prog id with
    | None -> f
    | Some vd -> 
	if is_static_field vd then f
	else 
	  (match f with
	     | Binder(Lambda, [(x, tf)], f') ->
		 let et = initial_value_of_type prog None false tf in
		   Hashtbl.add vm x et;
		   f'
	     | _ -> failwith ("handle_dependent_var did not expect " ^ 
				(PrintForm.string_of_form f) ^ "\n")) in
  let _ = debug_msg "\n" in
  let elhs = get_result fm vm id in
  let _ = debug_msg "\n" in
  let erhs = result_of_form prog fm vm f' in
  let min = min_esc_type elhs erhs in
  let _ = set_result fm vm id min in
  let _ = set_form_result prog fm vm f' min in
    debug_msg ("\n\n");
    ()

let analyze_methods 
    (prog : program) 
    (impl : impl_module) 
    (fm : (ident, esc_type) Hashtbl.t) 
    (vardefs : specvar_def list) : bool * ident list =
  let cg = build_call_graph prog impl in
  let orig_wl = mk_work_list prog impl in
  let cache = Hashtbl.create (List.length orig_wl) in
  let rec analyze (curr_wl : work list) : unit =
    debug_msg (string_of_work_list curr_wl);
    match curr_wl with
      | [] -> ()
      | w :: rest ->
	  let old_fm = Hashtbl.copy fm in
	  let new_work = analyze_method prog impl cg fm cache w in
	    (*
	  let _ = print_cache cache in
	    print_string ("New work " ^ (string_of_work_list new_work)); 
	    *)
	    if state_unchanged old_fm fm then
	      let new_wl = Util.union rest new_work in
		analyze new_wl
	    else
	      (let _ = Hashtbl.clear cache in
	       let _ = List.iter (handle_dependent_var prog impl fm) vardefs in
		 analyze orig_wl)
  in
  let _ = analyze orig_wl in
  let succeeded, failed = List.partition (successful_methods cache) orig_wl in
  let nums = List.length succeeded in
  let numf = List.length failed in
    (nums > numf, (List.map mname_of_work failed))
	
let initialize_fields 
    (prog : program) (impl : impl_module) : (ident, esc_type) Hashtbl.t =
  (* let fields = List.filter is_concrete_vd (collect_all_fields prog) in *)
  let fields = collect_all_fields prog in
  let field_map = Hashtbl.create (List.length fields) in
  let _ = List.iter (mk_initial_value prog impl field_map) fields in
    field_map

let is_static_method (mn : ident) (pd : proc_def) : bool =
  not (List.exists (fun vd -> vd.vd_name = this_id) pd.p_locals)

let is_static_class (prog : program) (impl : impl_module) : bool =
  match impl.im_owner with
    | Some _ -> false
    | None ->
	let spec = must_find_sm impl.im_name prog in
	  List.for_all is_static_field spec.sm_spec_vars &&
	    List.for_all is_static_field impl.im_vars &&
	    List.for_all (is_static_method impl.im_name) impl.im_procs

let is_field_of_class 
    (prog : program) (impl : impl_module) (id : ident) : bool =
  match find_var id impl.im_vars with
    | Some _ -> true
    | None -> 
	(match find_sm impl.im_name prog with
	   | Some sm ->
	       (match find_var id sm.sm_spec_vars with
		  | Some _ -> true
		  | None -> false)
	   | None -> false)

let allowable_public_state 
    (prog : program) (impl : impl_module) (id : ident) : bool =
  (id = str_tree) ||
    (id = str_rtrancl) ||
    (id = str_trancl) ||
    (id = arrayStateId) ||
    (is_field id prog) ||
    (is_valid_class prog id)

let public_state (prog : program) (impl : impl_module) (id : ident) : bool =
  not (is_field_of_class prog impl id) &&
    not (allowable_public_state prog impl id) &&
    not (id = "Object.alloc")

let rec get_field_id (f : form) : ident =
  match f with
    | Var v -> v
    | TypedForm(f', _) -> get_field_id f'
    | _ -> failwith ("get_field_id did not expect " ^
		       (MlPrintForm.string_of_form f))
	
let is_private_field 
    (field_map : (ident, esc_type) Hashtbl.t) (fld : ident) : bool =
  let result = Hashtbl.find field_map fld in
    match result with
      | ObjET (TPrivate, _) -> true
      | _ -> false

let transform_form
    (prog : program)
    (impl : impl_module)
    (field_map : (ident, esc_type) Hashtbl.t)
    (f : form) : form =
  let _ = print_string ("Transforming: " ^ (PrintForm.string_of_form f) ^ "\n") 
  in
  let privateStateId = impl.im_name ^ ".private" in
  let mk_private (id : ident) : form =
    mk_elem(Var id, Var privateStateId)
  in
  let rec transform 
      (bvs : ident list) (b : bool) (f : form) : form * ident list =
    match f with
      | Const _ -> (f, [])
      | Var v ->
	  if is_field_of_class prog impl v then
	    (App(Const FieldRead, [f; this_var]), [])
	  else if (List.mem v bvs) || (allowable_public_state prog impl v) then
	    (f, [])
	  else
	    failwith ("public state: " ^ (PrintForm.string_of_form f))
      | App(Const FieldRead, [fld; (Var v as obj)])
      | App(Const FieldRead, [fld; (TypedForm(Var v, _) as obj)]) ->
	  let fld', vs1 = transform bvs b fld in
	  let obj', vs2 = transform bvs b obj in
	  let vs = Util.union vs1 vs2 in
	  let vs' = if List.mem v bvs then vs @ [v] else vs in
	    (App(Const FieldRead, [fld'; obj']), vs')
      | App(Const FieldRead, [fld; obj]) ->
	  let fld', vs1 = transform bvs b fld in
	  let obj', vs2 = transform bvs b obj in
	    (App(Const FieldRead, [fld'; obj']), Util.union vs1 vs2)
      | App(Const ArrayRead, [arrSt; (TypedForm(Var v, tf) as arr); ind]) ->
	  let arrSt', vs1 = transform bvs b arrSt in
	  let arr', vs2 = transform bvs b arr in
	  let ind', vs3 = transform bvs b ind in
	  let vs = Util.union (Util.union vs1 vs2) vs3 in
	  let vs' = if List.mem v bvs then vs @ [v] else vs in
	    (App(Const ArrayRead, [arrSt'; arr'; ind']), vs')
      | App(Const Not, [f1]) -> 
	  let f1', vs = transform bvs (not b) f1 in
	    (App(Const Not, [f1']), vs)
      | App(Const (UMinus as op), fs)
      | App(Const (Ite as op), fs)
      | App(Const (Or as op), fs)
      | App(Const (FiniteSetConst as op), fs)
      | App(Const (Tuple as op), fs)
      | App(Const (And as op), fs) ->
	  let b' = if op = Or then not b else b in
	  let fs', vs = List.split (List.map (transform bvs b') fs) in
	    (App(Const op, fs'), (List.fold_left Util.union [] vs))
      | App(Const Subset as op,
	    [(Var v as f1); 
	     (TypedForm(Var "Object.alloc", _) as f2)])
      | App(Const Subseteq as op,
	    [(Var v as f1); 
	     (TypedForm(Var "Object.alloc", _) as f2)])
      | App(Const Elem as op, 
	    [(Var v as f1); 
	     (TypedForm(Var "Object.alloc", _) as f2)]) ->
	  let f1', vs = transform bvs b f1 in
	  let f' = App(op, [f1'; f2]) in
	    if b then
	      (f', vs)
	    else if List.mem v bvs then
	      (f', Util.set_add v vs)
	    else
	      failwith ("incorrect arity: " ^ (PrintForm.string_of_form f))
      | App(Const Subset as op, 
	    [f1; (TypedForm(Var "Object.alloc", _) as f2)])
      | App(Const Subseteq as op, 
	    [f1; (TypedForm(Var "Object.alloc", _) as f2)])
      | App(Const Elem as op, 
	    [f1; (TypedForm(Var "Object.alloc", _) as f2)]) ->
	  let f1', vs = transform bvs b f1 in
	    if b then
	      (App(op, [f1'; f2]), vs)
	    else
	      failwith ("incorrect arity: " ^ (PrintForm.string_of_form f))
      | App(Const Plus as op, [f1; f2])
      | App(Const Cup as op, [f1; f2])
      | App(Const Subset as op, [f1; f2])
      | App(Const Subseteq as op, [f1; f2])
      | App(Const Elem as op, [f1; f2])
      | App(Const Lt as op, [f1; f2])
      | App(Const LtEq as op, [f1; f2])
      | App(Const Gt as op, [f1; f2])
      | App(Const GtEq as op, [f1; f2])
      | App(Const Eq as op, [f1; f2]) ->
	  let f1', vs1 = transform bvs b f1 in
	  let f2', vs2 = transform bvs b f2 in
	    (App(op, [f1'; f2']), Util.union vs1 vs2)
      | App(Const Impl as op, [f1; f2]) -> 
	  let f1', vs1 = transform bvs (not b) f1 in
	  let f2', vs2 = transform bvs b f2 in
	    (App(op, [f1'; f2']), Util.union vs1 vs2)
      | App(TypedForm(Var "tree", _), [App(Const ListLiteral, fs)]) ->
	  let flds = List.map get_field_id fs in
	    if List.for_all (is_private_field field_map) flds then
	      (f, [])
	    else 
	      (mk_bool b, [])
      | App(TypedForm(Var "rtrancl_pt", _), fs) ->
	  (** ?? **)
	  failwith ("TODO")
      | App((TypedForm(Var _, _) as f1), [(Var v as f2)])
      | App((TypedForm(Var _, _) as f1), [(TypedForm(Var v, _) as f2)]) ->
	  let f1', vs1 = transform bvs b f1 in
	  let f2', vs2 = transform bvs b f2 in
	  let vs = Util.union vs1 vs2 in
	  let vs' = if List.mem v bvs then vs @ [v] else vs in
	    (App(f1', [f2']), vs')
      | App((TypedForm(Var _, _) as f1), fs) ->
	  let f1', vs1 = transform bvs b f1 in
	  let fs', vs = List.split (List.map (transform bvs b) fs) in
	  let vs' = List.fold_left Util.union [] vs in
	    (App(f1', fs'), Util.union vs1 vs')
      | TypedForm(f1, tf) -> 
	  let f1', vs = transform bvs b f1 in 
	    (TypedForm(f1', tf), vs)
      | Binder(Lambda as bdr, til, f1)
      | Binder(Comprehension as bdr, til, f1)
      | Binder(Exists as bdr, til, f1)
      | Binder(Forall as bdr, til, f1) ->
	  (* add constraints for comprehension *)
	  let bvs', _ = List.split til in
	  let b' = if bdr = Exists then not b else b in
	  let f1', vs = transform (Util.union bvs bvs') b' f1 in
	    if vs = [] then
	      (Binder(bdr, til, f1'), vs)
	    else
	      let vs1, vs2 = List.partition (fun x -> List.mem x bvs') vs in
	      let lhs = smk_and (List.map mk_private vs1) in
		(Binder(bdr, til, smk_impl (lhs, f1')), vs2)
      | _ -> 
	  failwith ("transform did not expect: " ^ 
		      (MlPrintForm.string_of_form f))

  in
  let fvs = List.filter (public_state prog impl) (fv f) in
  let _ = List.iter (fun x -> print_string ("fv: " ^ x ^ "\n")) fvs in
  let result = if fvs = [] then fst (transform [] true f) else mk_true in
    print_string ("\nTransformed: " ^ (PrintForm.string_of_form result) ^ "\n\n");
    result

let transform_vardef 
    (prog : program)
    (impl : impl_module)
    (field_map : (ident, esc_type) Hashtbl.t)
    ((x, f) : ident * form) : ident * form =
  print_string (x ^ " == " ^ (PrintForm.string_of_form f) ^ "\n");
  (x, transform_form prog impl field_map f)

let transform_inv
    (prog : program)
    (impl : impl_module)
    (field_map : (ident, esc_type) Hashtbl.t)
    (inv : Specs.invariant_desc) : Specs.invariant_desc =
  {inv with 
     Specs.inv_form = transform_form prog impl field_map inv.Specs.inv_form}
	
let transform_impl 
    (prog : program) 
    (impl : impl_module) 
    (field_map : (ident, esc_type) Hashtbl.t) 
    (failed_methods : ident list) : unit =
  let new_impl =
    {impl with
       im_vars = List.map (fun x -> {x with vd_field = false}) impl.im_vars;
       im_vardefs = 
	List.map (transform_vardef prog impl field_map) impl.im_vardefs;
       im_constdefs = 
	List.map (transform_vardef prog impl field_map) impl.im_constdefs;
       im_invs = List.map (transform_inv prog impl field_map) impl.im_invs} in
    ()

let analyze_impl (prog : program) (impl : impl_module) : unit =
  let _ = print_string ("Analyzing module " ^ impl.im_name ^ "...\n") in
    if is_static_class prog impl then
      let field_map = initialize_fields prog impl in
      let vardefs = collect_all_vardefs prog in
      let _ = List.iter (handle_dependent_var prog impl field_map) vardefs in
      let _ = debug_msg ("Initialized field map:\n") in
      let _ = print_analysis_state field_map in
      let success, failed_methods = 
	analyze_methods prog impl field_map vardefs in
      let failed_methods_str = String.concat ", " failed_methods in
	if success then
	  let msg = if failed_methods = [] then ".\n\n"
	  else ("\nexcept for these methods: " ^ failed_methods_str ^ "\n\n") in
	    print_string ("Module " ^ impl.im_name ^ " is instantiable" ^ msg);
	    transform_impl prog impl field_map failed_methods
	else 
	  print_string ("Module " ^ impl.im_name ^ " is not instantiable.\n" ^
			  "The following methods failed:\n" ^ 
			  failed_methods_str)
    else
      print_string ("Module " ^ impl.im_name ^ " is not a static class.\n\n")

let analyze_program (prog : program) (mnames : string list) : unit =
  let impls = List.map (fun x -> must_find_im x prog) mnames in
    List.iter (analyze_impl prog) impls;
    exit 0

