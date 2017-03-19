open Ast
open Form

(* Note: The interpreter needs to be given a well-formed program
   including the correct access of variables based on permissions
   (public/private/etc.). These checks are done when the ast is
   resolved. *)

(* Debugging for this module. *)
let debug_id : int = Debug.register_debug_module "Interpreter"
let debug_msg : (string -> unit) = Debug.debug_msg debug_id
let debug_is_on () : bool = Debug.debug_is_on debug_id

exception NullPointer
exception Returned
exception Termination
exception InterpreterFailure of string

(* Constants *)
let rtranclId = "rtrancl_pt"
let old_rtranclId = FormUtil.oldname rtranclId

let treeId = "tree"

let allocatedId = all_alloc_objs
let old_allocatedId = FormUtil.oldname allocatedId

let class_type = TypeApp(TypeSet, [(TypeApp(TypeObject,[]))])
let alloc_type = TypeApp(TypeSet, [(TypeApp(TypeObject,[]))])

type type_t = string
type field_name_t = string

type value_t =
  | SpecVar of form   (* definition of specification variables *)
  | BValue of bool
  | IValue of int
  | OValue of ref_t
  | SValue of value_t list
  | TValue of value_t list

and ref_t = {
  mutable reference : (obj_t ref) option;
  mutable name_of_type : type_t option;
}

and obj_t = {
  mutable obj : object_t;
  hashcode : int
}

and object_t =
  | Arr of typeForm * field_t * (value_t array)
  | Str of string
  | Obj of typeForm * (field_t list)

and field_t = 
    field_name_t * value_t

type var_t = {
  mutable value : value_t;
}

(* Stack frame *)
type frame_t = (ident * var_t) list

(* Stack *)
type stack_t = frame_t list

type inv_t = {
  mutable i_invs : form list;  (* The loop invariants we are testing. *)
  i_lc : loop_command; (* The corresponding loop. *)
}

(* There are three types of stores we need to track to support the old
   construct: 1) Stores to fields; 2) Stores to arrays; and 3) Stores
   to global variables. *)
type store_addr_t =
  | FStore of (value_t) * field_name_t
  | AStore of (value_t) * int
  | GStore of ident

type store_frame_t = (store_addr_t, value_t) Hashtbl.t

let make_new_store_frame () : store_frame_t =
  Hashtbl.create 10

(* This data structure keeps the interpreter state. *)
type state_t = {
  prog : program;
  to_check : inv_t option;
  mutable result : value_t option; (* Return value, if any. *)
  mutable stack : stack_t;
  mutable globals : frame_t;
  mutable alloc_objs : value_t list list; (* Stack of lists of all allocated objects *)
  fields : (field_name_t, var_decl) Hashtbl.t;
  mutable store_stack : store_frame_t list;
  classes : type_t list;
}

(* This data structure keeps track of the environment for evaluating
   formulas. *)
type env_t = {
  mutable e_env : frame_t;
  e_alloc_objs : value_t list list;
  e_fields : (field_name_t, var_decl) Hashtbl.t;
  e_store : store_frame_t;
  e_classes : type_t list;
}

let push_store_frame (st : state_t) : unit =
  let sf = make_new_store_frame () in
    st.store_stack <- sf :: st.store_stack

let merge_store_frames (tf : store_frame_t) (nf : store_frame_t) : unit =
  let add_to_nf (sa : store_addr_t) (v : value_t) : unit =
    if not (Hashtbl.mem nf sa) then Hashtbl.add nf sa v in
    Hashtbl.iter add_to_nf tf
      
let pop_store_frame (st : state_t) : unit =
  match st.store_stack with
    | sf0 :: (sf1 :: sfs) -> 
        merge_store_frames sf0 sf1; 
        st.store_stack <- sf1 :: sfs
    | _ -> raise (InterpreterFailure "pop_store_frame: stack underflow")

let get_top_store_frame (st : state_t) : store_frame_t =
  match st.store_stack with
    | sf :: _ -> sf
    | _ -> 
	raise (InterpreterFailure "get_top_store_frame: stack underflow")

let push_alloc_stack (st : state_t) : unit =
  st.alloc_objs <- [] :: st.alloc_objs

let pop_alloc_stack (st : state_t) : unit =
  match st.alloc_objs with
    | fr0 :: fr1 :: frs -> (* merge the top two frames *)
	st.alloc_objs <- (fr0 @ fr1) :: frs
    | _ -> raise (InterpreterFailure "pop_alloc_stack: stack underflow")

(* Keep track of all allocated objects. *)
let add_allocated_object (st : state_t) (v : value_t) : unit =
  match st.alloc_objs with
    | fr0 :: frs -> st.alloc_objs <- (v :: fr0) :: frs
    | _ -> 
	raise (InterpreterFailure "add_allocated_object: stack underflow")

(* Pretty printer for values. *)
let rec string_of_value (v : value_t) (d : int) : string =
  match v with
    | SpecVar f -> "(SpecVar " ^ (PrintForm.string_of_form f) ^ ")"
    | BValue b -> "(BValue " ^ (string_of_bool b) ^ ")"
    | IValue i -> "(IValue " ^ (string_of_int i) ^ ")"
    | OValue o -> "(OValue " ^ (string_of_ref_t o (d - 1)) ^ ")"
    | SValue s -> "(SValue {" ^ (string_of_valuel "" s (d - 1)) ^ "})"
    | TValue t -> "(TValue (" ^ (string_of_valuel "" t (d - 1)) ^ "))"
and string_of_valuel (s : string) (vs : value_t list) (d : int) : string =
  match vs with
    | [] -> s
    | [v] -> s ^ (string_of_value v d)
    | v :: vs0 -> 
	string_of_valuel (s ^ (string_of_value v d) ^ ", ") vs0 d
and string_of_ref_t (r : ref_t) (d : int) : string =
  let res = match r.reference with
    | None -> "null"
    | Some o -> string_of_obj !o d in
    match r.name_of_type with
      | None -> res
      | Some t -> "(" ^ res ^ " : " ^ t ^ ")"
and string_of_obj (o : obj_t) (d : int) : string =
  let result = "h" ^ string_of_int o.hashcode in
    if (d >= 0) then result ^ " " ^ (string_of_object o.obj d)
    else result
and string_of_object (o : object_t) (d : int) : string =
  match o with
    | Arr (_, _, arr) -> "[" ^ (string_of_values arr d) ^ "]"
    | Str s -> "\"" ^ s ^"\""
    | Obj (_, fields) -> "{" ^ (string_of_fields fields d) ^ "}"
and string_of_values (vs : value_t array) (d : int) : string =
  let append_value (s : string) (v : value_t) : string =
    (s ^ " " ^ (string_of_value v d) ^ ";") in
    Array.fold_left append_value "" vs
and string_of_field ((n,v) : field_t) (d : int) : string =
  (" " ^ n ^ " := " ^ (string_of_value v d) ^ ";")
and string_of_fields (fields : field_t list) (d : int) : string =
  let append_field (s : string) (f : field_t) : string =
    (s ^ (string_of_field f d)) in
    List.fold_left append_field "" fields

let string_of_v (v : value_t) : string =
  string_of_value v 1

let is_int_value (v : value_t) : bool =
  match v with
    | IValue _ -> true
    | _ -> false

let int_of_value (v : value_t) : int =
  match v with
    | IValue i -> i
    | _ -> let err = "int_of_value did not expect " ^ (string_of_v v) in
	raise (InterpreterFailure err)

let is_specvar_value (v : value_t) : bool =
  match v with
    | SpecVar _ -> true
    | _ -> false

let array_of_value (v : value_t) : value_t array =
  let err = "array_of_value did not expect " ^ (string_of_v v) in
    match v with
      | OValue o ->
	  (match o.reference with
	     | Some r ->
		 (match (!r).obj with
		    | Arr (_, _, arr) -> arr
		    | _ -> raise (InterpreterFailure err))
	     | None -> raise NullPointer)
      | _ -> raise (InterpreterFailure err)

let form_of_value (v : value_t) : form =
  match v with
    | SpecVar f -> f
    | _ -> let err = "form_of_value did not expect " ^ (string_of_v v) in
	raise (InterpreterFailure err)

let nullObject () : value_t = 
  OValue {reference = None; name_of_type = None}

let nullConst : value_t = nullObject ()

let string_of_store_addr (sa : store_addr_t) : string =
  match sa with
    | FStore (v, fn) -> "(field " ^ fn ^ " of " ^ (string_of_v v) ^ ")"
    | AStore (v, i) -> 
	"(array " ^ (string_of_v v) ^ "[" ^ (string_of_int i) ^ "])"
    | GStore id -> "(static field: " ^ id ^ ")"

let string_of_store_frame (s : string) (sf : store_frame_t) : string =
  let string_of_entry 
      (sa : store_addr_t) (v : value_t) (s : string) : string =
    s^"\t"^(string_of_store_addr sa)^" := "^(string_of_v v)^"\n" in
    s ^ (Hashtbl.fold string_of_entry sf "STORE FRAME:\n")

let string_of_store_stack (ss : store_frame_t list) : string =
  (List.fold_left string_of_store_frame "STORE STACK:\n" ss)
    
let fetch_from_store_frame 
    (sf : store_frame_t) (sa : store_addr_t) : value_t =
  let result = Hashtbl.find sf sa in
    debug_msg ("fetch_from_store_frame: " ^ (string_of_store_addr sa) ^ 
		 " := " ^ (string_of_v result) ^ "\n");
    result

let not_in_store_frame 
    (sf : store_frame_t) (sa : store_addr_t) : bool =
  not (Hashtbl.mem sf sa)

let put_in_store_frame
    (sf : store_frame_t) (sa : store_addr_t) (v : value_t) : unit =
  if (not_in_store_frame sf sa) then
    (debug_msg ("put_in_store_frame: " ^ (string_of_store_addr sa) ^ 
		  " := " ^ (string_of_v v) ^ "\n");
     Hashtbl.add sf sa v)

(* Save away the old value if we haven't already done so. *)
let note_store (st : state_t) (sa : store_addr_t) (v : value_t) : unit =
  let sf = get_top_store_frame st in
    put_in_store_frame sf sa v

let note_store_in_env 
    (env : env_t) (sa : store_addr_t) (v : value_t) : unit =
  put_in_store_frame env.e_store sa v

let alloc_objs_of_env (env : env_t) : value_t list =
  List.flatten env.e_alloc_objs

let old_alloc_objs_of_env (env : env_t) : value_t list =
  List.flatten (List.tl env.e_alloc_objs)

let default_of_type (tf0 : typeForm) : value_t =
  match tf0 with
    | TypeApp(TypeInt, []) -> IValue 0
    | TypeApp(TypeBool, []) -> BValue false
    | TypeApp(TypeString, [])
    | TypeApp(TypeObject, []) -> nullObject ()
    | TypeApp(TypeSet, _) -> SValue []
	(* TODO: handle arrays and other types *)
    | _ -> let err = "default_of_type did not expect " ^ 
	(MlPrintForm.string_of_type tf0) in
	raise (InterpreterFailure err)

let is_ghost (vd : var_decl) : bool =
  vd.vd_ghost

let is_concrete (vd : var_decl) : bool =
  not vd.vd_abstract

let is_static_field (vd : var_decl) : bool =
  (not vd.vd_field)

let is_object_field (vd : var_decl) : bool =
  vd.vd_field

let ident_of_var_decl (vd : var_decl) : ident =
  vd.vd_name

let tf_of_var_decl (vd : var_decl) : typeForm =
  vd.vd_type

let default_of_var_decl (vd : var_decl) : value_t =
  default_of_type vd.vd_type

let default_of_field (vd : var_decl) : value_t =
  debug_msg ((PrintForm.string_of_type vd.vd_type) ^ "\n");
  match vd.vd_type with
    | TypeApp(TypeArray,[(TypeApp(TypeObject,[])); ty]) ->
	default_of_type ty
    | _ -> let err = "default_of_field did not expect " ^ 
	(PrintForm.string_of_type vd.vd_type) in
	raise (InterpreterFailure err)

let string_of_field_tbl (env : env_t) : string =
  let string_of_field_entry 
      (fn : field_name_t) (vd : var_decl) (str : string) : string =
    str ^ fn ^ " := " ^ (PrintAst.pr_var_decl vd) ^ "\n" in
    "FIELDS:\n" ^ (Hashtbl.fold string_of_field_entry env.e_fields "")

let get_default_field_value (env : env_t) (fn : field_name_t) : value_t =
  try
    let vd = Hashtbl.find env.e_fields fn in
      default_of_field vd
  with Not_found -> 
    print_string (string_of_field_tbl env);
    let err = "get_default_field_value could not find " ^ fn in
      raise (InterpreterFailure err)
    
let push_stack_frame (st : state_t) : unit =
  st.stack <- [] :: st.stack

let pop_stack_frame (st : state_t) : unit =
  match st.stack with
    | [] -> raise (InterpreterFailure "pop_stack_frame: stack is empty")
    | fr :: frs -> st.stack <- frs

let rec value_equal (v0 : value_t) (v1 : value_t) : bool =
  match v0, v1 with
    | (OValue {reference = Some r0}), (OValue {reference = Some r1}) -> 
	r0 == r1
    | (SValue s0), (SValue s1) ->
	(List.length s0 = List.length s1) && (values_equal s0 s1)
    | _ -> v0 = v1
and values_equal (s0 : value_t list) (s1 : value_t list) : bool =
  match s0 with
    | [] -> true
    | x0 :: s0' -> 
	let succeeded, s1' = remove_match x0 [] s1 in
	  succeeded && (values_equal s0' s1')
and remove_match 
    (v : value_t) (s0 : value_t list) (s1 : value_t list) : 
    bool * value_t list =
  match s1 with
    | [] -> false, s0
    | x :: s2 ->
	if (value_equal v x) then
	  true, (s0 @ s2)
	else 
	  remove_match v (s0 @ [x]) s2

let assign (st : state_t) (id : ident) (v : value_t) : unit =
  match st.stack with
    | [] -> raise (InterpreterFailure "assign: stack underflow.")
    | fr :: _ ->
	try
	  let var = List.assoc id fr in
	    debug_msg ("assign: " ^ id ^ " := " ^ (string_of_v v) ^ "\n\n");
	    var.value <- v
	with Not_found ->
	  let var = List.assoc id st.globals in
	    if (not (value_equal var.value v)) then
	      (debug_msg ("assign global: " ^ id ^ " := " ^ (string_of_v v) ^ "\n\n");
	       note_store st (GStore id) var.value; (* save old value first *)
	       var.value <- v)

let make_result (st : state_t) (v : value_t) : unit =
  match st.stack with
    | [] -> raise (InterpreterFailure "assign: stack underflow.")
    | fr :: frs ->
	let fr0 = (Ast.result_var, {value = v}) :: fr in
	  st.stack <- fr0 :: frs

let assign_old (st : state_t) (id : ident) (v : value_t) : unit =
  st.globals <- (id, {value = v;}) :: st.globals

let assign_in_env (env : env_t) (id : ident) (v : value_t) : unit =
  debug_msg ("assign_in_env: " ^ id ^ " := " ^ (string_of_v v) ^ "\n\n");
  (* This will mask any variables of the same name that already
     exists, without changing their values. *)
  env.e_env <- (id, {value = v}) :: env.e_env

let has_type (v : value_t) (cn : type_t) : bool =
  match v with
    | OValue r ->
	(match r.name_of_type with
	   | None -> true
	   | Some ty0 -> 
	       debug_msg ("get_type: " ^ (string_of_v v) ^ " : " ^ 
			       ty0 ^ "\n"); 
	       (cn = ty0))
    | BValue _ -> (cn = "boolean")
    | IValue _ -> (cn = "int")
    | _ -> let err = "get_type: cannot get type of " ^ (string_of_v v) in
	raise (InterpreterFailure err)

let make_default (vd : var_decl) : ident * var_t =
  let id = vd.vd_name in
  let v = default_of_var_decl vd in
    debug_msg ("initializing: " ^ id ^ " := " ^ (string_of_v v) ^ "\n");
    (id, {value = v;})

let specvars_of_mapping (m : mapping) : specvar_def list =
  m.map_abst

let specvars_of_impl (im : impl_module) : specvar_def list =
  im.im_constdefs @ im.im_vardefs 
    
let specvars_of_spec (sm : spec_module) : specvar_def list =
  sm.sm_constdefs @ sm.sm_vardefs

let get_spec_var_formula (st : state_t) (vd : var_decl) : form =
  let id = vd.vd_name in
  let specvars = List.flatten
    ((List.map specvars_of_mapping st.prog.p_maps) @
       (List.map specvars_of_impl st.prog.p_impls) @
       (List.map specvars_of_spec st.prog.p_specs)) in
    List.assoc id specvars

let remove_top_lambda (f : form) : form =
  match f with
    | Binder(Lambda, til, f0) ->
	let bound, _ = List.split til in
	let fv = FormUtil.fv f0 in
	let intersection = Util.intersect bound fv in
	  if (intersection = []) then f0
	  else let err = "remove_top_lambda: bound variables in " ^
	    (PrintForm.string_of_form f) in
	    raise (InterpreterFailure err)
    | _ -> let err = "remove_top_lambda: can't find lambda " ^ 
	(PrintForm.string_of_form f) in
	raise (InterpreterFailure err)

let make_spec_var (st : state_t) (vd : var_decl) : ident * var_t =
  let id = vd.vd_name in
  let v = SpecVar (get_spec_var_formula st vd) in
    debug_msg ("specvar init: " ^ id ^ " := " ^ (string_of_v v) ^ "\n");
    (id, {value = v;})

let make_assign ((vd, v) : (var_decl * value_t)) : ident * var_t =
  debug_msg ("\nmake_assign: " ^ (PrintAst.pr_var_decl vd) ^ "\n");
  (vd.vd_name, {value = v;})

let create_vars (st : state_t) (vds : var_decl list) : unit =
  match st.stack with
    | [] -> raise (InterpreterFailure "create_vars: stack is empty.")
    | fr :: frs ->
	let fr0 = List.map make_default vds in
	  st.stack <- (fr0 @ fr) :: frs

let create_spec_vars (st : state_t) (svs : specvar_def list) : unit =
  match st.stack with
    | [] -> raise (InterpreterFailure "create_vars: stack is empty.")
    | fr :: frs ->
	let fr0 = List.map (fun (id, f) -> (id, {value = SpecVar f})) svs in
	  st.stack <- (fr0 @ fr) :: frs

let create_args 
    (st : state_t) (vds : var_decl list) (args : value_t list) : unit =
  match st.stack with
    | [] -> raise (InterpreterFailure "create_args: stack is empty.")
    | fr :: frs ->
	let fr0 = List.map make_assign (List.combine vds args) in
	  st.stack <- (fr0 @ fr) :: frs

let create_global (st : state_t) (vd : var_decl) : ident * var_t =
  if ((is_concrete vd) || (is_ghost vd)) then
    make_default vd
  else
    make_spec_var st vd

let create_globals (st : state_t) (vds : var_decl list) : unit =
  debug_msg "\ncreate_globals\n";
  let is_not_duplicate (vd : var_decl) : bool =
    not (List.mem_assoc vd.vd_name st.globals) in
  let vds0 = List.filter is_not_duplicate vds in
  let fr0 = List.map (create_global st) vds0 in
    st.globals <- fr0 @ st.globals

let get_var (env : env_t) (id : ident) : var_t =
  List.assoc id env.e_env

let write_field 
    (env : env_t) 
    (fname :field_name_t) 
    (o : value_t) 
    (v : value_t) : unit =
  debug_msg ("write_field: write field " ^ fname ^ " of " ^ 
	       (string_of_v o) ^ " with value " ^ (string_of_v v) ^ 
	       "\n\n");
  let err = "write_field: " ^ fname ^ " not found in " ^ (string_of_v o) in
    (match o with
       | OValue r ->
	   (match r.reference with
	      | Some o1 ->
		  (match (!o1).obj with
		     | Obj (tf, fds) ->
			 (try
			    let ov = List.assoc fname fds in
			    let fds0 = List.remove_assoc fname fds in
			    let f0 = (fname, v) in
			      if (not (value_equal ov v)) then
				(note_store_in_env env (FStore (o, fname)) ov;
				 (!o1).obj <- Obj (tf, (f0 :: fds0)))
			  with Not_found -> raise (InterpreterFailure err))
		     | _ -> raise (InterpreterFailure err))
	      | None -> raise NullPointer)
       | _ -> raise (InterpreterFailure err));
    debug_msg ("Result of write is:\n\t" ^ (string_of_v o) ^ "\n")

let read_field
    (env : env_t) (fname : field_name_t) (v : value_t) : value_t =
  let default_value () : value_t = get_default_field_value env fname in
    match v with
      | OValue r ->
	  (match r.reference with
	     | Some o ->
		 (match (!o).obj with
		    | Arr (_, (f, v0), _) -> 
			if (f = fname) then v0
			else default_value ()
		    | Obj (_, fs) ->
			(try
			   List.assoc fname fs
			 with Not_found -> default_value ())
		    | _ -> default_value ())
	     | None -> default_value ())
      | _ -> default_value ()

let read_possibly_old_field
    (env : env_t) (fname : field_name_t) (v : value_t) : (value_t * bool) =
  let is_old = FormUtil.is_oldname fname in
  let fname = if is_old then (FormUtil.unoldname fname) else fname in
  let result =
    if is_old then
      try
	fetch_from_store_frame env.e_store (FStore (v, fname))
      with Not_found -> read_field env fname v
    else read_field env fname v in
    result, is_old

let write_array 
    (env : env_t) (arr : value_t) (ind : value_t) (v : value_t) : unit =
  debug_msg ("write_array : " ^ (string_of_v arr) ^ "[" ^ 
	       (string_of_v ind) ^ "] := " ^ (string_of_v v) ^ "\n\n");
  let ind0 = int_of_value ind in
  let arr0 = array_of_value arr in
    if (not (value_equal v arr0.(ind0))) then
      (note_store_in_env env (AStore (arr, ind0)) arr0.(ind0);
       arr0.(ind0) <- v)

(* Due to the peculiar quirks of the Jahob specification language, a
   field read of a null object produces null. *)
let read_array (arr : value_t) (ind : value_t) : value_t =
  try
    let ind0 = int_of_value ind in
    let arr0 = array_of_value arr in
    let res = arr0.(ind0) in
      debug_msg ("read_array : " ^ (string_of_v arr) ^ "[" ^ 
		   (string_of_v ind) ^ "] = " ^ (string_of_v res) ^ 
		   "\n\n");
      res
  with NullPointer -> nullObject ()

let read_old_array 
    (env : env_t) (arr : value_t) (ind : value_t) : value_t =
  try
    fetch_from_store_frame env.e_store (AStore (arr, (int_of_value ind)))
  with Not_found ->
    read_array arr ind

let bool_of_value (v : value_t) : bool =
  match v with
    | BValue b -> b
    | _ -> let err = "bool_of_value did not get a boolean: " ^ 
	(string_of_v v) in
	raise (InterpreterFailure err)
	  
let set_of_value (v : value_t) : value_t list =
  match v with
    | SValue s -> s
    | _ -> let err = "set_of_value did not get a set: " ^ 
	(string_of_v v) in
	raise (InterpreterFailure err)
	  
let negate (v : value_t) : value_t =
  BValue (not (bool_of_value v))

let rec field_name_of_form (f : form) : field_name_t =
  match f with
    | Var v -> v
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> field_name_of_form f0
    | _ -> let err = "field_name_of_form: cannot interpret " ^
	(PrintForm.string_of_form f) in
	raise (InterpreterFailure err)

let rec array_or_field_write (f : form) : bool =
  match f with
    | App(Const FieldWrite, _)
    | App(Const ArrayWrite, _) -> true
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> array_or_field_write f0
    | _ -> false

let value_subset (v0 : value_t) (v1 : value_t) : bool =
  match v0, v1 with
    | (SValue s0), (SValue s1) ->
	(List.length s0 < List.length s1) && (values_equal s0 s1)
    | _ -> let err = "value_subset only operates on sets:\n\t" ^ 
	(string_of_v v0) ^ "\n\t" ^ (string_of_v v1) in
	raise (InterpreterFailure err)

let value_subseteq (v0 : value_t) (v1 : value_t) : bool =
  match v0, v1 with
    | (SValue s0), (SValue s1) ->
	(List.length s0 <= List.length s1) && (values_equal s0 s1)
    | _ -> let err = "value_subseteq only operates on sets:\n\t" ^ 
	(string_of_v v0) ^ "\n\t" ^ (string_of_v v1) in
	raise (InterpreterFailure err)

let value_list_diff 
    (s0 : value_t list) (s1 : value_t list) : value_t list =
  let not_in_s1 (v : value_t) : bool =
    not (List.exists (value_equal v) s1) in
    List.filter not_in_s1 s0

let value_diff (v0 : value_t) (v1 : value_t) : value_t =
  let s0 = set_of_value v0 in
  let s1 = set_of_value v1 in
    SValue (value_list_diff s0 s1)
      
let value_list_union 
    (s0 : value_t list) (s1 : value_t list) : value_t list =
  s0 @ (value_list_diff s1 s0)

let value_union (v0 : value_t) (v1 : value_t) : value_t =
  let s0 = set_of_value v0 in
  let s1 = set_of_value v1 in
    SValue (value_list_union s0 s1)

let value_inter (v0 : value_t) (v1 : value_t) : value_t =
  let s0 = set_of_value v0 in
  let s1 = set_of_value v1 in
  let in_s0 (v : value_t) : bool =
    List.exists (value_equal v) s0 in
    SValue (List.filter in_s0 s1)

let value_elem (v0 : value_t) (v1 : value_t) : bool =
  let s1 = set_of_value v1 in
    List.exists (value_equal v0) s1

let in_alloc_objs_of_env (env : env_t) (v : value_t) : bool =
  value_elem v (SValue (alloc_objs_of_env env))

let in_old_alloc_objs_of_env (env : env_t) (v : value_t) : bool =
  value_elem v (SValue (old_alloc_objs_of_env env))

let evaluate_op 
    (op : constValue) (v0 : value_t) (v1 : value_t) : value_t =
  match op with
    | Cardeq | Eq | Seteq -> BValue (value_equal v0 v1)
    | Lt -> BValue ((int_of_value v0) < (int_of_value v1))
    | Gt -> BValue ((int_of_value v0) > (int_of_value v1))
    | Cardleq | LtEq -> BValue ((int_of_value v0) <= (int_of_value v1))
    | Cardgeq | GtEq -> BValue ((int_of_value v0) >= (int_of_value v1))
    | Plus -> IValue ((int_of_value v0) + (int_of_value v1))
    | Minus ->
	if (is_int_value v0) then
	  IValue ((int_of_value v0) - (int_of_value v1))
	else value_diff v0 v1
    | Mult -> IValue ((int_of_value v0) * (int_of_value v1))
    | Div -> IValue ((int_of_value v0) / (int_of_value v1))
    | Mod -> IValue ((int_of_value v0) mod (int_of_value v1))
    | Subseteq -> BValue (value_subseteq v0 v1)
    | Subset -> BValue (value_subset v0 v1)
    | Cup -> value_union v0 v1
    | Cap -> value_inter v0 v1
    | Diff -> value_diff v0 v1
    | _ -> let err = "evaluate: don't know how to evaluate formula" in
	raise (InterpreterFailure err)

let is_simple_op (op : constValue) : bool =
  match op with 
    | Eq | Seteq | Lt | Gt | LtEq | GtEq 
    | Plus | Minus | Mult | Div | Mod | Subseteq | Subset | Cup | Cap 
    | Diff -> true
    | _ -> false

let rec is_var_of_id (id : ident) (f : form) : bool =
  match f with
    | Var id0 -> id = id0
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> is_var_of_id id f0
    | _ -> false

let rec is_lambda (f : form) : bool =
  match f with
    | Binder(Lambda, _, _) -> true
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> is_lambda f0
    | _ -> false

let rec get_to_form (f : form) : form =
  match f with
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> get_to_form f0
    | _ -> f

let is_treeness_op (f : form) : bool =
  is_var_of_id treeId f

let is_rtrancl_op (f : form) : bool =
  is_var_of_id rtranclId f

let is_old_rtrancl_op (f : form) : bool =
  is_var_of_id old_rtranclId f

let is_rtrancl (f : form) : bool =
  is_rtrancl_op f || is_old_rtrancl_op f

let rec ident_of_form (f : form) : ident =
  match f with
    | Var v -> v
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> ident_of_form f0
    | _ -> let err = "ident_of_form did not expect " ^
	(PrintForm.string_of_form f) in
	raise (InterpreterFailure err)

let is_classname (env : env_t) (f : form) : bool =
  try
    let id = ident_of_form f in
    let id = if (FormUtil.is_oldname id) then 
      (FormUtil.unoldname id) else id in
      List.mem id env.e_classes
  with InterpreterFailure _ -> false
    
let increment_form (f : form) : form =
  FormUtil.mk_plus (f, (FormUtil.mk_int 1))

let no_such_fvs (f : form) (ids : ident list) : bool =
  let fv = FormUtil.fv f in
    List.for_all (fun id -> (not (List.mem id fv))) ids

(* Returns (lb, f) where x <= lb and f is the rest of the formula. *)
let get_lower_bound 
    (ind : ident) (ids : ident list) (f : form) : form * form =
  let rec get_lower_bound_rec (f : form) : form option * form option =
    match f with
      | App(Const And, fs0) ->
	  let fo, fs0' = handle_and fs0 in
	  let f' = FormUtil.smk_and fs0' in
	    (fo, Some f')
      | App(Const Impl, [f0; f1]) ->
	  let fo, f0o = get_lower_bound_rec f0 in
	    (match f0o with
	      | None -> (fo, Some f1)
	      | Some f0' ->
		  let f' = FormUtil.smk_impl (f0', f1) in
		    (fo, Some f'))
      | App(Const Eq, [f0; f1]) 
	  when (is_var_of_id ind f0) && (no_such_fvs f1 (ind :: ids)) ->
	  (Some f1, Some f) (* Leave f as an upper bound. *)
      | App(Const Eq, [f1; f0]) 
	  when (is_var_of_id ind f0) && (no_such_fvs f1 (ind :: ids)) ->
	  (Some f1, Some f) (* Leave f as an upper bound. *)
      | App(Const GtEq, [f0; f1]) 
      | App(Const LtEq, [f1; f0]) 
	  when (is_var_of_id ind f0) && (no_such_fvs f1 (ind :: ids)) ->
	  (Some f1, None)
      | App(Const Gt, [f0; f1]) 
      | App(Const Lt, [f1; f0]) 
	  when (is_var_of_id ind f0) && (no_such_fvs f1 (ind :: ids)) ->
	  (Some (increment_form f1), None)
      | _ -> (None, Some f)
  and handle_and (fs : form list) : form option * form list =
    match fs with
      | [] -> None, []
      | f :: fs0 ->
	  let lbo, fo = get_lower_bound_rec f in
	  let lbo, fs0' =
	    match lbo with
	      | Some lb -> lbo, fs0
	      | None -> handle_and fs0 in
	    match fo with
	      | Some f' -> (lbo, f' :: fs0')
	      | None -> (lbo, fs0') in
  let lbo, fo = get_lower_bound_rec f in
    match lbo with
      | None -> let err = "No lower bound for " ^ ind ^ " in " ^
	  (PrintForm.string_of_form f) in
	  raise (InterpreterFailure err)
      | Some lb ->
	  match fo with
	    | None -> (lb, FormUtil.mk_true)
	    | Some f' -> (lb, f')

(* Returns (ub, f) where ind < ub and f is the rest of the formula. *)
let get_upper_bound 
    (ind : ident) (ids : ident list) (f : form) : form * form =
  let rec get_upper_bound_rec (f : form) : form option * form option =
    match f with
      | App(Const And, fs0) ->
	  let fo, fs0' = handle_and fs0 in
	  let f' = FormUtil.smk_and fs0' in
	    (fo, Some f')
      | App(Const Impl, [f0; f1]) ->
	  let fo, f0o = get_upper_bound_rec f0 in
	    (match f0o with
	       | None -> (fo, Some f1)
	       | Some f0' ->
		   let f' = FormUtil.smk_impl (f0', f1) in
		     (fo, Some f'))
      | App(Const Eq, [f0; f1]) 
      | App(Const LtEq, [f0; f1]) 
      | App(Const GtEq, [f1; f0]) 
	  when (is_var_of_id ind f0) && (no_such_fvs f1 (ind :: ids)) ->
	  (Some (increment_form f1), None)
      | App(Const Eq, [f1; f0]) 
	  when (is_var_of_id ind f0) && (no_such_fvs f1 (ind :: ids)) ->
	  (Some (increment_form f1), None)
      | App(Const Lt, [f0; f1]) 
      | App(Const Gt, [f1; f0]) 
	  when (is_var_of_id ind f0) && (no_such_fvs f1 (ind :: ids)) ->
	  ((Some f1), None)
      | _ -> (None, Some f)
  and handle_and (fs : form list) : form option * form list =
    match fs with
      | [] -> None, []
      | f :: fs0 ->
	  let lbo, fo = get_upper_bound_rec f in
	  let lbo, fs0' =
	    match lbo with
	      | Some lb -> lbo, fs0
	      | None -> handle_and fs0 in
	    match fo with
	      | Some f' -> (lbo, f' :: fs0')
	      | None -> (lbo, fs0') in
  let lbo, fo = get_upper_bound_rec f in
    match lbo with
      | None -> let err = "No upper bound for " ^ ind ^ " in " ^
	  (PrintForm.string_of_form f) in
	  raise (InterpreterFailure err)
      | Some lb ->
	  match fo with
	    | None -> (lb, FormUtil.mk_true)
	    | Some f' -> (lb, f')

let get_definition (elem : ident) (f : form) : form * form =
  let rec get_definition_rec (f : form) : form * form option =
    match f with
      | App(Const Eq, [f0; f1]) 
	  when (is_var_of_id elem f0) && 
	    not (List.mem elem (FormUtil.fv f1)) ->
	  (f1, None)
      | App(Const Eq, [f0; f1]) 
	  when (is_var_of_id elem f1) && 
	    not (List.mem elem (FormUtil.fv f0)) ->
	  (f0, None)
      | App(Const And, fs) ->
	  let def, fs' = handle_and fs in
	  let f' = FormUtil.smk_and fs' in
	    (def, Some f')
      | App(Const Impl, [f0; f1]) ->
	  let def, fo = get_definition_rec f0 in
	    (match fo with
	       | None -> (def, Some f1)
	       | Some f0' ->
		   let f' = FormUtil.smk_impl (f0', f1) in
		     (def, Some f'))
      | _ -> raise Not_found
  and handle_and (fs : form list) : form * form list = 
    match fs with
      | [] -> raise Not_found
      | f :: fs' ->
	  try
	    let def, fo = get_definition_rec f in
	      (match fo with
		 | None -> (def, fs')
		 | Some f' -> (def, (f' :: fs')))
	  with Not_found -> 
	    let def, fs'' = handle_and fs' in
	      (def, (f :: fs'')) in 
  let def, fo = get_definition_rec f in
    match fo with
      | None -> def, FormUtil.mk_true
      | Some f' -> (def, f')

let rec make_indices (lb : int) (ub : int) : int list =
  if (lb < ub) then
    lb :: (make_indices (lb + 1) ub)
  else []

(* Returns (rt, f) where rt is a recursive transitive closure
   definition of elem and f is the rest of the formula. *)
let get_rtrancl (elem : ident) (f : form) : form * form =
  let rec get_rtrancl_rec (f : form) : form option * form option =
    match f with
      | App(Const And, fs0) ->
	  let fo, fs0' = handle_and fs0 in
	  let f' = FormUtil.smk_and fs0' in
	    (fo, Some f')
      | App(Const Impl, [f0; f1]) ->
	  let fo, f0o = get_rtrancl_rec f0 in
	    (match f0o with
	       | None -> (fo, Some f1)
	       | Some f0' ->
		   let f' = FormUtil.smk_impl (f0', f1) in
		     (fo, Some f'))
      | App(op, [f0; f1; f2]) when (is_rtrancl op) ->
	  (Some f, None)
      | _ -> (None, Some f)
  and handle_and (fs : form list) : form option * form list =
    match fs with
      | [] -> None, []
      | f :: fs0 ->
	  let lbo, fo = get_rtrancl_rec f in
	  let lbo, fs0' =
	    match lbo with
	      | Some lb -> lbo, fs0
	      | None -> handle_and fs0 in
	    match fo with
	      | Some f' -> (lbo, f' :: fs0')
	      | None -> (lbo, fs0') in
  let lbo, fo = get_rtrancl_rec f in
    match lbo with
      | None -> raise Not_found
      | Some lb ->
	  match fo with
	    | None -> (lb, FormUtil.mk_true)
	    | Some f' -> (lb, f')

let rec rename_bound_variables (f : form) : form =
  match f with
    | Binder(Lambda, til, f0) ->
	let ids, tys = List.split til in
	let ids0 = List.map Util.fresh_name ids in
	let vs = List.map FormUtil.mk_var ids0 in
	let sm = List.combine ids vs in
	let f0' = FormUtil.subst sm (rename_bound_variables f0) in
	let til0 = List.combine ids0 tys in
	  Binder(Lambda, til0, f0')
    | _ -> f

let curr_hashcode = ref 0
let next_hashcode () : int =
  curr_hashcode := !curr_hashcode + 1; !curr_hashcode
 
let is_field (env : env_t) (f : form) : bool =
  try
    let id = ident_of_form f in
    let id = if (FormUtil.is_oldname id) then 
      FormUtil.unoldname id 
    else id in
      Hashtbl.mem env.e_fields id
  with InterpreterFailure _ -> false

let object_of_type (cls : ident) (v : value_t) : bool =
  match v with
    | BValue _ -> cls = "boolean"
    | IValue _ -> cls = "int"
    | OValue r -> 
	(match r.name_of_type with
	   | Some n -> cls = n
	   | None -> false)
    | _ -> false

let check_parents_and_acyclicity 
    (env : env_t) (fns : field_name_t list) (objs : value_t list) : bool =
  let rec check_acyclicity 
      (wl : value_t list) (acc : value_t list) : bool =
    match wl with
      | [] -> true
      | obj :: wl0 ->
	    let children = List.map (fun x -> read_field env x obj) fns in
	    let children = List.filter
	      (fun x -> not (value_equal x nullConst)) children in
	    let not_in_acc (v : value_t) : bool =
	      List.for_all (fun x -> not (value_equal v x)) acc in
	      (List.for_all not_in_acc children) &&
		(check_acyclicity (wl0 @ children) (acc @ children)) in
  let rec check_rec 
      (to_check : value_t list) (checked : value_t list) : bool =
    match to_check with
      | obj :: to_check0 ->
	  (* First, check that each node has zero or one parent. *)
	  let children = List.map (fun x -> read_field env x obj) fns in
	  let children = List.filter
	    (fun x -> not (value_equal x nullConst)) children in
	  let not_in_checked (v : value_t) : bool =
	    List.for_all (fun x -> not (value_equal v x)) checked in
	    (List.for_all not_in_checked children) &&
	      (check_rec to_check0 (checked @ children))
      | [] -> (* Check acyclicity using the set of roots computed. *)
	  let roots = value_list_diff objs checked in
	    check_acyclicity roots [] in
    check_rec objs []
  
let check_treeness (env : env_t) (fs : form list) : value_t =
  let field_names = List.map field_name_of_form fs in
  let cls = Util.unqualify_getting_module (List.hd field_names) in
  let objs = List.filter (object_of_type cls) (alloc_objs_of_env env) in
  let result = check_parents_and_acyclicity env field_names objs in
    debug_msg ("\nCheck treeness:\n");
    List.iter (fun x -> debug_msg ("tree? " ^ (string_of_v x) ^ "\n")) objs;
    if result then debug_msg ("Treeness check succeeded.\n")
    else debug_msg ("Treeness check failed.\n");
    BValue result

let apply_lambda (lambda : form) (args : form list) : form =
  match lambda with
    | Binder(Lambda, til, f0) ->
	let til0, til1 = Util.unappend til (List.length args) in
	let ids, _ = List.split til0 in
	let sm = List.combine ids args in
	let f1 = FormUtil.subst sm f0 in
	  if til1 = [] then f1 else Binder(Lambda, til1, f1)
    | _ -> let err = "apply_lambda cannot be applied to non-lambda " ^
	(PrintForm.string_of_form lambda) in
	raise (InterpreterFailure err)

let rec apply_if_lambda (f : form) : form =
  match f with
    | App(f0, fs) when (is_lambda f0) -> apply_lambda (get_to_form f0) fs
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> apply_if_lambda f0
    | Binder(b, til, f0) ->
	Binder(b, til, (apply_if_lambda f0))
    | App(f0, fs) ->
	App((apply_if_lambda f0), (List.map apply_if_lambda fs))
    | _ -> f
	
let rec interpret_form (env : env_t) (f : form) : value_t =
  debug_msg ("interpret_form: " ^ (PrintForm.string_of_form f) ^ "\n\n");
  match f with
    | Const EmptysetConst -> SValue []
    | Const (BoolConst b) -> BValue b
    | Const (IntConst i) -> IValue i
    | Const (StringConst s) -> 
	OValue {reference = Some (ref {obj = Str s; 
				       hashcode = next_hashcode ()}); 
		name_of_type = None}
    | Const NullConst -> OValue {reference = None; name_of_type = None}
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> interpret_form env f0
    | Var v ->
	let result = get_value env v in
	  debug_msg ("Var "^v^" has value:\n"^(string_of_v result)^"\n\n");
	  result
    | App(Const Tuple, fs) -> TValue (List.map (interpret_form env) fs)
    | App(Const Not, [f0]) -> negate (interpret_form env f0)
    | App(Const UMinus, [f0]) ->
	IValue (- (int_of_value (interpret_form env f0)))
    | App(Const MetaAnd, fs)
    | App(Const And, fs) ->
	let rec evaluate_and (fs : form list) : value_t =
	  match fs with
	    | [] -> BValue true
	    | f0 :: fs0 -> 
		let result = interpret_form env f0 in
		  if (bool_of_value result) then
		    evaluate_and fs0
		  else 
		    (debug_msg ("And: " ^ (PrintForm.string_of_form f0) ^
				  " is false\n");
		     result) in
	  evaluate_and fs
    | App(Const Or, fs) ->
	let rec evaluate_or (fs : form list) : value_t =
	  match fs with
	    | [] -> BValue false
	    | f0 :: fs0 ->
		let result = interpret_form env f0 in
		  if (bool_of_value result) then
		    result
		  else evaluate_or fs0 in
	  evaluate_or fs
    | App(Const FieldRead, [field; obj]) ->
	let fname = field_name_of_form field in
	let v1 = interpret_form env obj in
	let result, is_old = read_possibly_old_field env fname v1 in
	let result = match result with
	  | SpecVar f0 -> 
	      let f0 = if is_old then 
		FormUtil.oldify true [] f0 else f0 in
	      let f1, _ = TypeReconstruct.reconstruct_types [] f0 in
		interpret_form env (App(f1, [obj]))
	  | _ -> result in
	  debug_msg ("Result of:\n\t" ^ (PrintForm.string_of_form f) ^
		       "\n is " ^ (string_of_v result) ^ "\n\n");
	  result
    | App(Const ArrayRead, [gao; arr; ind]) ->
	let arr0 = interpret_form env arr in
	let ind0 = interpret_form env ind in
	  if (FormUtil.is_oldname (ident_of_form gao)) then
	    read_old_array env arr0 ind0
	  else read_array arr0 ind0
    | App(Const Elem, [f0; App(Const Cap, [f1; f2])]) ->
	let f3 = FormUtil.mk_elem (f0, f1) in
	let f4 = FormUtil.mk_elem (f0, f2) in
	  interpret_form env (FormUtil.smk_and [f3; f4])
    | App(Const Elem, [f0; App(Const Cup, [f1; f2])]) ->
	let f3 = FormUtil.mk_elem (f0, f1) in
	let f4 = FormUtil.mk_elem (f0, f2) in
	  interpret_form env (FormUtil.smk_or [f3; f4])
    | App(Const Elem, [f0; App(Const Diff, [f1; f2])]) ->
	let f3 = FormUtil.mk_elem (f0, f1) in
	let f4 = FormUtil.smk_not (FormUtil.mk_elem (f0, f2)) in
	  interpret_form env (FormUtil.smk_and [f3; f4])
    | App(Const Elem, [f0; f1]) when (is_var_of_id allocatedId f1) ->
	let v0 = interpret_form env f0 in
	  BValue (in_alloc_objs_of_env env v0)
    | App(Const Elem, [f0; f1]) when (is_var_of_id old_allocatedId f1) ->
	let v0 = interpret_form env f0 in
	  BValue (in_old_alloc_objs_of_env env v0)
    | App(Const Elem, [f0; f1]) when (is_classname env f1) ->
	let v0 = interpret_form env f0 in
	let cn = ident_of_form f1 in
	  if (FormUtil.is_oldname cn) then
	    let cn = FormUtil.unoldname cn in
	      BValue ((has_type v0 cn) && (in_alloc_objs_of_env env v0))
	  else BValue (has_type v0 cn)
    | App(Const Elem, [f0; f1]) -> interpret_elem env f0 f1
    | App(Const Card, [f0]) ->
	let v0 = interpret_form env f0 in
	  IValue (Array.length (array_of_value v0))
    | App(Const (Cardeq as op), [f0; f1])
    | App(Const (Cardleq as op), [f0; f1]) 
    | App(Const (Cardgeq as op), [f0; f1]) ->
	let v0 = interpret_form env f0 in
	let c0 = Array.length (array_of_value v0) in
	let v1 = interpret_form env f1 in
	  evaluate_op op (IValue c0) v1 
    | App(Const FiniteSetConst, fs) ->
	SValue (List.map (interpret_form env) fs)
    | App(Const MetaImpl, [f0; f1])
    | App(Const Impl, [f0; f1]) ->
	let antecedent = interpret_form env f0 in
	  if (bool_of_value antecedent) then
	    interpret_form env f1
	  else BValue true
    | App(Const MetaEq, [f0; f1])
    | App(Const Iff, [f0; f1]) ->
	let v0 = interpret_form env (App(Const Impl, [f0; f1])) in
	let v1 = interpret_form env (App(Const Impl, [f1; f0])) in
	  BValue ((bool_of_value v0) && (bool_of_value v1))
    | App(Const Ite, [f0; f1; f2]) ->
	let v0 = interpret_form env f0 in
	  if (bool_of_value v0) then
	    interpret_form env f1
	  else interpret_form env f2
    | App(Const op, [f0; f1]) when (is_simple_op op) ->
	let v0 = interpret_form env f0 in
	let v1 = interpret_form env f1 in
	  evaluate_op op v0 v1
    | App(op, [App(Const ListLiteral, fs)]) when (is_treeness_op op) ->
	check_treeness env fs
    | App(op, _) when (is_rtrancl op) -> SpecVar f
    | App(op, [f]) when (is_field env op) ->
	interpret_form env (App(Const FieldRead, [op; f]));
    | App(f0, fs) ->
	let lambda = form_of_value (interpret_form env f0) in
	let f' = apply_lambda lambda fs in
	  interpret_form env f'
    | Binder(Comprehension, [(id, ty)], f0) ->
	(* This preprocessing makes the set comprehension computation
	   more efficient because then we can use pattern-matching. *)
	let restrict_to_specvar 
	    (sm : FormUtil.substMap) (id : ident) : FormUtil.substMap =
	  try
	    let v = interpret_form env (Var id) in
	      if (is_specvar_value v) then
		sm @ [(id, (form_of_value v))]
	      else sm
	  with _ -> sm in
	let sm = List.fold_left restrict_to_specvar [] (FormUtil.fv f) in
	let f1 = apply_if_lambda (FormUtil.subst sm f0) in
	  (try
	     interpret_comprehension env id ty f1
	   with err -> 
	     if (FormUtil.fv f) = [] then SpecVar f else raise err)
    | Binder(Forall, til, f0) ->
	debug_msg ("Forall: " ^ (PrintForm.string_of_form f) ^ "\n\n");
	(match til with
	   | (id, TypeApp(TypeObject, [])) :: til0 ->
	       let f0' = if (til0 = []) then f0 
	       else Binder(Forall, til0, f0) in
		 (try
		    let d0, f1 = get_definition id f0' in
		      interpret_in_env env [id] f1 [(interpret_form env d0)]
		  with Not_found ->
		    interpret_forall env id f0' (alloc_objs_of_env env))
	   | (id, TypeApp(TypeInt, [])) :: til0 ->
	       let lb, f1 = get_lower_bound id [] f0 in
	       let ub, f2 = get_upper_bound id [] f1 in
	       let indices = make_value_indices env lb ub in
		 interpret_forall env id f2 indices
	   | _ -> let err = "interpret_form can't handle " ^
	       (MlPrintForm.string_of_form f) in
	       raise (InterpreterFailure err))
    | Binder(Exists, til, f0) ->
	(match til with
	   | (id, TypeApp(TypeObject, [])) :: til0 ->
	       let f0' = if (til0 = []) then f0
	       else Binder(Exists, til0, f0) in
		 (try
		    let d0, f1 = get_definition id f0' in
		      interpret_in_env env [id] f1 [(interpret_form env d0)]
		  with Not_found ->
		    interpret_exists env id f0' (alloc_objs_of_env env))
	   | _ -> let err = "interpret_form can't handle " ^ 
	       (MlPrintForm.string_of_form f) in
	       raise (InterpreterFailure err))
    | Binder(Lambda, _, _) -> SpecVar f 
    | _ -> let err = "interpret_form can't handle " ^ 
	(MlPrintForm.string_of_form f) in
	raise (InterpreterFailure err)

and execute_form (env : env_t) (f : form) : unit =
  debug_msg ("execute_form: " ^ (MlPrintForm.string_of_form f) ^ "\n\n");
  match f with
    | Const (BoolConst true) -> ()
    | Const (BoolConst false) -> raise Termination
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> execute_form env f0
    | App(Const And, fs) ->
	List.iter (execute_form env) fs
    | App(Const ArrayWrite, [_; arr; ind; value]) ->
	let arr0 = interpret_form env arr in
	let ind0 = interpret_form env ind in
	let val0 = interpret_form env value in
	  write_array env arr0 ind0 val0
    | App(Const FieldWrite, [field; obj; value]) ->
	let fname = field_name_of_form field in
	let v1 = interpret_form env obj in
	let v2 = interpret_form env value in
	  write_field env fname v1 v2
    | App(Const Elem, [_; f1]) 
	when (is_var_of_id allocatedId f1) || (is_classname env f1) ->
	() (* These are hints to vcgen. Can ignore. *)
    | _ -> let err = "execute_form can't handle:\n\t" ^ 
	(PrintForm.string_of_form f) in
	raise (InterpreterFailure err)

and get_old_value (env : env_t) (id : ident) : value_t =
  try
    fetch_from_store_frame env.e_store (GStore id)
  with Not_found ->
    let var = get_var env id in
      match var.value with
	| SpecVar f -> 
	    let f = FormUtil.oldify true [] f in
	    let f, _ = TypeReconstruct.reconstruct_types [] f in
	      interpret_form env f
	| _ -> var.value
	    
and get_value (env : env_t) (id : ident) : value_t =
  if (FormUtil.is_oldname id) then
    get_old_value env (FormUtil.unoldname id)
  else let var = get_var env id in
    match var.value with
      | SpecVar f -> 
	  let f, _ = TypeReconstruct.reconstruct_types [] f in
	    interpret_form env f
      | _ -> var.value

and interpret_elem (env : env_t) (f0 : form) (f1 : form) : value_t =
  match f1 with
    | Binder(Comprehension, [(id, _)], f) ->
	interpret_form env (FormUtil.subst [(id, f0)] f)
    | _ ->
	let v1 = interpret_form env f1 in
	  match v1 with
	    | SpecVar f -> interpret_elem env f0 f
	    | _ ->
		let v0 = interpret_form env f0 in
		  BValue (value_elem v0 v1)

and constrain (env : env_t) (c : form) (id : ident) (f : form) : bool =
  let c' = FormUtil.subst [(id, f)] c in
    bool_of_value (interpret_form env c')

and interpret_comprehension 
    (env : env_t) (id : ident) (ty : typeForm) (f : form) : value_t = 
  debug_msg ("interpret_comprehension over " ^ id ^ " of " ^
	       (PrintForm.string_of_form f) ^ "\n");
  let satisfies_form (f : form) (x : value_t) : bool =
    bool_of_value (interpret_in_env env [id] f [x]) in
  let last_resort (f : form) : value_t =
    debug_msg ("Try last resort for " ^ (PrintForm.string_of_form f) ^ "\n");
    if (ty = TypeApp(TypeObject, [])) then
      SValue (List.filter (satisfies_form f) (alloc_objs_of_env env))
    else
      let err = "interpret_comprehensions: can't handle " ^
	(PrintForm.string_of_form f) in
	raise (InterpreterFailure err) in
    match (get_to_form f) with
      | Binder(Exists, [(i, (TypeApp(TypeInt, [])))], f0) ->
	  let make_element (f : form) (ind : form) : form =
	    FormUtil.subst [(i, ind)] f in
	  let lb, f1 = get_lower_bound i [id] f0 in
	  let ub, f2 = get_upper_bound i [id] f1 in
	  let indices = make_form_indices env lb ub in
	  let def, f3 = get_definition id f2 in
	  let elem_fs = List.map (make_element def) indices in
	  let elem_fs = List.filter (constrain env f3 id) elem_fs in
	  let elem_vs = List.map (interpret_form env) elem_fs in
	    SValue elem_vs
      | App(Const Or, fs) ->
	  let vs = List.map (interpret_comprehension env id ty) fs in
	    List.fold_left value_union (SValue []) vs
      | App(Const And, fs) ->
	  (try
	     let def, f0 = get_definition id f in
	       if (constrain env f0 id def) then
		 SValue [(interpret_form env def)]
	       else SValue []
	   with Not_found ->
	     try
	       let rt, f0 = get_rtrancl id f in
		 value_of_rtrancl env id rt f0
	     with Not_found -> last_resort f)
      | App(op, fs) when (is_rtrancl op) ->
	  let rt, f0 = get_rtrancl id f in
	    value_of_rtrancl env id rt f0
      | _ -> last_resort f

and make_form_indices (env : env_t) (lb : form) (ub : form) : form list =
  let lb0 = int_of_value (interpret_form env lb) in
  let ub0 = int_of_value (interpret_form env ub) in
    List.map FormUtil.mk_int (make_indices lb0 ub0)
      
and make_value_indices 
    (env : env_t) (lb : form) (ub : form) : value_t list =
  let lb0 = int_of_value (interpret_form env lb) in
  let ub0 = int_of_value (interpret_form env ub) in
    List.map (fun x -> IValue x) (make_indices lb0 ub0)
      
and value_of_rtrancl 
    (env : env_t) (id : ident) (rt : form) (tlf : form) : value_t =
  let incorrect_form (f : form) : string =
    "value_of_rtrancl: formula of incorrect form:\n\t" ^
      (PrintForm.string_of_form f) in
  let rec generate_elements
      (toSubId : ident) 
      (seedf : form)
      (rtranclf : form) : value_t list =
    let rec generate_elements_rec 
	(deff : form) (* formula defining elements *)
	(conf : form) (* formula constraining elements *)
	(wl : form list) (* work list of elements not yet processed *)
	(res : value_t list) : value_t list =
      let generate_rec = generate_elements_rec deff conf in
	match wl with
	  | [] -> res
	  | f :: wl0 ->
	      let f0 = FormUtil.subst [(toSubId, f)] deff in
		if ((constrain env conf id f0) &&
		      (constrain env tlf id f0)) then
		  let v0 = interpret_form env f0 in
		    if (List.exists (value_equal v0) res) then
		      generate_rec wl0 res
		    else generate_rec (wl0 @ [f0]) (res @ [v0])
		else generate_rec wl0 res in
      match rtranclf with
	| App(Const Or, fs) ->
	    let generate = generate_elements toSubId seedf in
	    let result = List.map generate fs in
	      List.fold_left value_list_union [] result
	| App(Const Eq, _)
	| App(Const And, _) ->
	    let genf, cf = get_definition id rtranclf in
	      if ((constrain env cf id seedf) &&
		    (constrain env tlf id seedf)) then
		let seed = interpret_form env seedf in
		  generate_elements_rec genf cf [seedf] [seed] 
	      else [] 
	| _ -> raise (InterpreterFailure (incorrect_form rtranclf)) in
    match rt with
      | App(rtop, [f0; f1; f2]) when (is_rtrancl rtop) ->
	  (* We need to rename the bound variables to fresh variables
	     in case there are name conflicts because we are going to
	     perform substitution on the bound formula. *)
	  (match (rename_bound_variables f0) with
	     | Binder(Lambda, [(id0, _); (id1, _)], f0') ->
		 let elem, def, startf =
		   if (is_var_of_id id f1) then
		     id0, id1, f2
		   else id1, id0, f1 in
		 let subf = FormUtil.subst [(elem, (FormUtil.mk_var id))] f0' in
		 let elems = generate_elements def startf subf in
		   SValue elems
	     | _ -> raise (InterpreterFailure (incorrect_form f0)))
      | _ -> raise (InterpreterFailure (incorrect_form rt))

and interpret_in_env 
    (env : env_t) 
    (ids : ident list) 
    (f : form) 
    (xs : value_t list) : value_t =
  let fr = env.e_env in (* save original environment *)
    List.iter2 (assign_in_env env) ids xs;
    let result = interpret_form env f in
      env.e_env <- fr; (* restore original environment *)
      result

and interpret_forall 
    (env : env_t)
    (id : ident)
    (f : form)
    (xs : value_t list) : value_t =
  let rec interpret_forall_rec (xs : value_t list) : bool =
    match xs with
      | [] -> true
      | x :: xs0 -> 
	  let result = bool_of_value (interpret_in_env env [id] f [x]) in
	    result && (interpret_forall_rec xs0) in
    BValue (interpret_forall_rec xs)

and interpret_exists
    (env : env_t)
    (id : ident)
    (f : form)
    (xs : value_t list) : value_t =
  let rec interpret_exists_rec (xs : value_t list) : bool =
    match xs with
      | [] -> false
      | x :: xs0 ->
	  let result = bool_of_value (interpret_in_env env [id] f [x]) in
	    result || (interpret_exists_rec xs0) in
    BValue (interpret_exists_rec xs)
	      
let evaluate (st : state_t) (f : form) : value_t =
  let env = {e_env = (List.hd st.stack) @ st.globals; 
	     e_alloc_objs = st.alloc_objs; 
	     e_fields = st.fields;
	     e_store = List.hd st.store_stack;
	     e_classes = st.classes} in
  let f, _ = TypeReconstruct.reconstruct_types [] f in
  let result = interpret_form env f in
    debug_msg ("evaluated: " ^ (PrintForm.string_of_form f) ^ " to " ^ 
		 (string_of_v result) ^ "\n");
    result

let execute (st : state_t) (f : form) : unit =
  let env = {e_env = (List.hd st.stack) @ st.globals; 
	     e_alloc_objs = st.alloc_objs; 
	     e_fields = st.fields;
	     e_store = List.hd st.store_stack;
	     e_classes = st.classes} in
    execute_form env f

let find_false_conjuncts (st : state_t) (f : form) : form list =
  let rec find (f : form) : form list =
    match f with 
      | TypedForm(f1,_) | App(Const Comment, [_;f1]) -> find f1
      | App(Const And, f1::fs) | App(Const MetaAnd, f1::fs) ->
	  if bool_of_value (evaluate st f1) then 
	    find (App(Const And, fs))
	  else find f1
      | App(Const Or, fs) -> List.concat (List.map find fs)
      | _ ->
	  if bool_of_value (evaluate st f) then []
	  else [f]
  in find f

let check_form (st : state_t) (f : form) : bool =
  bool_of_value (evaluate st f)

let complain_about_subformula (fs : form list) =
  match fs with
    | [] -> Util.warn "Could not determine false subformula."
    | _ -> 
	print_string ("\nThese subformulas evaluated to false:\n");
	(List.iter 
	   (fun f ->
	      print_string (PrintForm.string_of_form f ^ "\n");
	      debug_msg ("i.e.\n" ^
			   MlPrintForm.string_of_form f ^ "\n"))
	   fs)

let assert_form (st : state_t) (f : form) : bool =
  if bool_of_value (evaluate st f) then true
  else
    let subf = find_false_conjuncts st (FormUtil.negation_normal_form f) in
      complain_about_subformula subf;
      false

(* This is the form we want to use for loop invariant inference, since
   we may have poorly-formed formulas. *)
let resilient_check_form (st : state_t) (f : form) : bool =
  try
    check_form st f
  with InterpreterFailure msg ->
    print_string ("\nWARNING: " ^ msg ^ "\n"); false
    | _ -> let msg = "\nWARNING: resilient_check_form failed on " ^ 
	(PrintForm.string_of_form f) in
	print_string msg; false

let field_of_vd (st : state_t) (vd : var_decl) : field_name_t * value_t =
  debug_msg ("field_of_vd: " ^ (PrintAst.pr_var_decl vd) ^ "\n");
  let v =
    (if ((is_concrete vd) || (is_ghost vd)) then
       match vd.vd_init with
	 | Some f -> evaluate st (remove_top_lambda f)
	 | None -> default_of_var_decl vd
     else
       SpecVar (get_spec_var_formula st vd)) in
    (vd.vd_name, v)

let instantiate_locals (st : state_t) (proc : proc_def) : unit =
  let vs = List.filter (fun x -> is_concrete x || is_ghost x) proc.p_locals in
    create_vars st vs;
    create_spec_vars st proc.p_vardefs
    
let instantiate_formals 
    (st : state_t) (proc : proc_def) (args : value_t list) : unit =
  create_args st proc.p_header.p_formals args

let allocate (st : state_t) ((id, tf0) : typedIdent) (ty : ident) : unit =
  let im = AstUtil.must_find_im ty st.prog in
  let sm = AstUtil.must_find_sm ty st.prog in
  let ifields = List.filter is_object_field im.im_vars in
  let sfields = List.filter is_object_field sm.sm_spec_vars in
  let fields = Util.union ifields sfields in
  let o = Obj (tf0, (List.map (field_of_vd st) fields)) in
  let p = {obj = o; hashcode = next_hashcode ()} in
  let r = OValue {reference = Some (ref p); name_of_type = Some ty} in
    add_allocated_object st r;
    (assign st id r)

let allocate_array 
    (st : state_t) 
    ((id, tf0) : typedIdent) 
    (ty : ident) 
    (dims : form list) : unit =
  let init_fun (x : int) = default_of_type tf0 in
    match dims with
      | [d] -> 
	  let len = evaluate st d in
	  let i = int_of_value len in
	  let field = (FormUtil.arrayLengthId, len) in
	  let arr = Array.init i init_fun in
	  let object_a = Arr (tf0, field, arr) in
	  let obj_a = {obj = object_a; hashcode = next_hashcode ()} in
	  let ref_a = OValue {reference = Some (ref obj_a); 
			      name_of_type = Some (FormUtil.arrayName)} in
	    add_allocated_object st ref_a;
	    assign st id ref_a
      | _ -> let err = "allocate_array: cannot handle arrays of " ^ 
	  (string_of_int (List.length dims)) ^ " dimensions" in
	  raise (InterpreterFailure err)

let evaluate_preconditions 
    (st : state_t) 
    (proc : proc_def) 
    (im : impl_module) 
    (ext : bool) : unit =
  let contract = proc.p_header.p_contract in
  let pre = 
    if ext then Sast.concretized_pre st.prog im proc.p_header
    else contract.co_pre in
  let failure = "\nThe following procedure precondition for " ^ 
    proc.p_header.p_name ^ " was not satisfied:\n\t" ^ 
    (PrintForm.string_of_form pre) in
  let _ = debug_msg ("Checking precondition: "^(PrintForm.string_of_form pre)^"\n\n") in
    try
      if (assert_form st pre) then 
	(print_string "["; flush_all ()) (* print progress *)
      else raise (InterpreterFailure failure)
    with InterpreterFailure err ->
      if (!Util.resilient) then
	print_string (err ^ failure ^ "\nContinuing to execute...\n")
	  (* Minor issue: duplicate error message. TOFIX *)
      else raise (InterpreterFailure (err ^ failure))

let evaluate_postconditions
    (st : state_t) 
    (proc : proc_def) 
    (im : impl_module) 
    (ext : bool) : unit =
  let contract = proc.p_header.p_contract in
  let post = 
    if ext then Sast.concretized_post st.prog im proc proc.p_header proc.p_body
    else contract.co_post in
  let failure = "\nThe following procedure postcondition for " ^ 
    proc.p_header.p_name ^ " was not satisfied:\n\t" ^
    (PrintForm.string_of_form post) in
    debug_msg ("Checking postcondition: "^(PrintForm.string_of_form post)^"\n\n");
    try
      if (assert_form st post) then 
	(print_string "]"; flush_all ()) (* print progress *)
      else print_string failure
    with InterpreterFailure err ->
      if (!Util.resilient) then
	print_string (err ^ failure ^ "\nContinuing to execute...\n")
      else raise (InterpreterFailure (err ^ failure))

let rec interpret_rec (st : state_t) (c : command) : unit =
  print_string "."; flush_all (); (* print progress *)
  debug_msg ("\ninterpreting: " ^ (PrintAst.pr_command c));
  match c with
    | Basic {bcell_cmd = bc} -> 
	(try
	   interpret_bc st bc
	 with NullPointer ->
	   let err = "NullPointerException: " ^ 
	     (PrintAst.pr_basic_cmd bc) in
	     raise (InterpreterFailure err)
	   | Termination -> ())
    | Seq cl -> List.iter (interpret_rec st) cl
    | Choice cl ->
	let n = Random.int (List.length cl) in
	let c0 = List.nth cl n in
	  interpret_rec st c0
    | If {if_condition = ic; if_then = it; if_else = ie} ->
	if (check_form st ic) then
	  interpret_rec st it
	else
	  interpret_rec st ie
    | Loop lc -> 
	(match st.to_check with
	   | None -> interpret_loop st lc
	   | Some inv ->
	       if (lc = inv.i_lc) then
		 interpret_and_check_loop st lc inv
	       else
		 interpret_loop st lc)
    | Return {return_exp = fo} ->
	(match fo with
	   | None -> ()
	   | Some f -> let result = evaluate st f in
	       make_result st result;
	       st.result <- Some result);
	raise Returned
    | Assuming _ -> Util.fail "interpret_rec: uncaught pattern matching case \
                               'Assuming'"
    | PickAny _ -> Util.fail "interpret_rec: uncaught pattern matching case \
                              'PickAny'"
    | PickWitness _ -> Util.fail "interpret_rec: uncaught pattern matching case \
                              'PickWitness'"
    | Induct _ -> Util.fail "interpret_rec: uncaught pattern matching case \
                             'Induct'"
    | Contradict _ -> Util.fail "interpret_rec: uncaught pattern matching case \
                                 'Contradict'"
    | Proof _ -> Util.fail "interpret_rec: uncaught pattern matching case \
                            'Proof'"

and interpret_and_check_loop 
    (st : state_t) (lc : loop_command) (inv : inv_t) : unit =
  print_string "-"; flush_all (); (* printing to show progress. *)
  interpret_rec st lc.loop_prebody;
  inv.i_invs <- List.filter (resilient_check_form st) inv.i_invs;
  if (check_form st lc.loop_test) then
    (interpret_rec st lc.loop_postbody;
     interpret_and_check_loop st lc inv)
      
and interpret_loop (st : state_t) (lc : loop_command) : unit =
  print_string "x"; flush_all (); (* printing to show progress. *)
  interpret_rec st lc.loop_prebody;
  (match lc.loop_inv with
     | None -> ()
     | Some inv ->
	 if (not (assert_form st inv)) then
	   let err = "Violation of user-supplied loop " ^
	     "invariant:\n\t" ^ (PrintForm.string_of_form inv) in
	     raise (InterpreterFailure err));
  if (check_form st lc.loop_test) then
    (interpret_rec st lc.loop_postbody;
     interpret_loop st lc)

and interpret_bc (st : state_t) (bc : basic_command) : unit =
  debug_msg (string_of_store_stack st.store_stack);
  match bc with
    | Skip
    | Hint _ (* This is a special statement used for Bohne. *) -> ()
    | Havoc hr -> let err = "interpret_bc:\n\tProcedures should " ^
	"not contain havocs:\n\t" ^ (PrintAst.pr_basic_cmd bc) in
	raise (InterpreterFailure err)
    | VarAssign {assign_lhs = lhs; assign_rhs = rhs} ->
	if (array_or_field_write rhs) then
	  execute st rhs
	else
	  assign st lhs (evaluate st rhs)
    | Alloc {alloc_tlhs = ti; alloc_type = ty} ->
	allocate st ti ty
    | ArrayAlloc {arr_alloc_tlhs = ti; arr_alloc_type = ty; arr_alloc_dims = d} ->
	allocate_array st ti ty d
    | Assert {hannot_form = f; hannot_msg = m}
    | NoteThat {hannot_form = f; hannot_msg = m} 
    | Split {annot_form = f; annot_msg = m} ->
	if (not (bool_of_value (evaluate st f))) then
	  let err = "interpret_bc:\n\tThe following assertion " ^
	    "evaluated to false:\n\t" ^ (PrintAst.pr_basic_cmd bc) in
	    if (!Util.resilient) then
	      print_string (err ^ "\nContinuing to execute...\n")
	    else raise (InterpreterFailure err)
    | Assume {annot_form = f; annot_msg = m} ->
	if (not (bool_of_value (evaluate st f))) then
	  let err = "interpret_bc:\n\tThe following assumption " ^
	    "evaluated to false:\n\t" ^ (PrintAst.pr_basic_cmd bc) ^
	    "\nContinuing to execute...\n" in
	    print_string err
    | ProcCall pc ->
	  invoke_procedure st pc
    | Instantiate _ ->
	Util.fail "interpret_bc: uncaught pattern matching case 'Instantiate'"
    | Mp _ -> 
	Util.fail "interpret_bc: uncaught pattern matching case 'Mp'"
	
and invoke_procedure (st : state_t) (pc : proc_call) : unit =
  debug_msg ("Invoking procedure " ^ pc.callee_name ^ "\n\n");
  let args = List.map (evaluate st) pc.callee_args in
  let im = AstUtil.must_find_im pc.callee_module st.prog in
  let proco = AstUtil.find_proc pc.callee_name im in
    match proco with
      | None -> let err = "invoke_procedure: cannot find proc_def" in
	  raise (InterpreterFailure err)
      | Some proc ->
	  try
	    push_stack_frame st;
	    push_store_frame st;
	    instantiate_formals st proc args;
	    instantiate_locals st proc;
	    evaluate_preconditions st proc im pc.call_is_external;
	    (try
	       interpret_rec st proc.p_body
	     with Returned -> ());
	    evaluate_postconditions st proc im pc.call_is_external;
	    pop_store_frame st;
	    pop_stack_frame st;
	    (match pc.callee_res, st.result with
	       | None, _ -> ()
	       | Some id, Some v -> assign st id v
	       | Some _, _ -> 
		   let err = "invoke_procedure missing result" in
		     raise (InterpreterFailure err));
	    st.result <- None;
	    debug_msg ("Returned from " ^ pc.callee_name ^ "\n")
	  with InterpreterFailure err ->
	    let err = "\n" ^ err ^ "\n\nin\t" ^ 
	      (PrintAst.pr_proc_header_line pc.callee_name proc.p_header) ^
	      "\n\n" in
	      raise (InterpreterFailure err)
		  
(* Instantitate static variables for a class. *)
let instantiate_globals (st : state_t) (vds : var_decl list) : unit =
  create_globals st (List.filter is_static_field vds)

let instantiate_classes (st : state_t) : unit =
  (* Instantiate static variables for each class. *)
  let im_vars = List.map (fun x -> x.im_vars) st.prog.p_impls in
  let sm_vars = List.map (fun x -> x.sm_spec_vars) st.prog.p_specs in
    List.iter (instantiate_globals st) im_vars;
    List.iter (instantiate_globals st) sm_vars

let collect_classes (prog : program) : type_t list =
  List.map (fun x -> x.im_name) prog.p_impls

let collect_fields (prog : program) : (field_name_t, var_decl) Hashtbl.t =
  let ifields = List.flatten (List.map (fun x -> x.im_vars) prog.p_impls) in
  let ifields = List.filter is_object_field ifields in
  let sfields = List.flatten (List.map (fun x -> x.sm_spec_vars) prog.p_specs) in
  let sfields = List.filter is_object_field sfields in
  let fields = Util.union ifields sfields in
  let field_names = List.map ident_of_var_decl fields in
  let field_tbl = Hashtbl.create (List.length fields) in
    List.iter2 (Hashtbl.add field_tbl) field_names fields;
    field_tbl
  
let interpret
    (prog : program)
    (proc : proc_def)
    (impl : impl_module)
    (to_check : inv_t option) : unit =
  let success = "\nThe execution completed successfully.\n\n" in
  let failure = 
    "\nThe execution could not be completed because of an error:\n" in
  let fields = collect_fields prog in
  let classes = collect_classes prog in
  let st = 
    {prog = prog; to_check = to_check; 
     result = None; stack = []; globals = []; 
     alloc_objs = [[nullObject ()]]; 
     fields = fields; store_stack = []; classes = classes} in
  let bpc = ref true in
  let apc = ref false in
    try
      push_stack_frame st;
      push_store_frame st;
      instantiate_classes st;
      bpc := false;
      evaluate_preconditions st proc impl true;
      apc := true;
      instantiate_locals st proc;
      (try
	 interpret_rec st proc.p_body;
       with Returned -> ());
      evaluate_postconditions st proc impl true;
      print_string success
    with InterpreterFailure err ->
      if ((not !apc) && (not !bpc)) then
	print_string ("\n\nSkipping interpretation of procedure " ^ 
			proc.p_header.p_name ^
			"\n(Preconditions not satisfied.)\n\n")
      else
	print_string (failure ^ err)

let test_invariants
    (prog : program)
    (impl : impl_module)
    (proc : proc_def)
    ((invs, lc) : form list * loop_command): form list =
  let inv = {i_invs = invs; i_lc = lc} in
  if (proc.p_header.p_formals = []) then
    (print_string ("\n\nInvoking interpreter for procedure: " ^ 
		     proc.p_header.p_name ^ "\n");
     interpret prog proc impl (Some inv);
     print_string ("Exit interpreter.\n");
     inv.i_invs)
  else
    (print_string ("\n\nSkipping interpretation of procedure " ^ 
		     proc.p_header.p_name ^ 
		     "\n(Interpreter must be run on procedures with no " ^
		     "arguments.)\n\n");
     print_string ("Exit interpreter.\n");
     [])

let test
    (prog : program)
    (impl : impl_module)
    (proc : proc_def) : unit =
  if (proc.p_header.p_formals = []) then
    (print_string ("\n\nInvoking interpreter for procedure: " ^ 
		     proc.p_header.p_name ^ "\n");
     interpret prog proc impl None)
  else
    print_string ("\n\nSkipping interpretation of procedure " ^ 
		    proc.p_header.p_name ^ 
		    "\n(Interpreter must be run on procedures with no " ^
		    "arguments.)\n\n");
  print_string ("Exit interpreter.\n")

(* THINGS TO DO *)
(* 1. Work on examples. *)
(* 2. Add more hooks for determining which portions of assertions are failing. *)
(* 3. Make rtrancl handling more general. *)
