open Ast
open AstUtil
open Form
open FormUtil
open Util

let debug_id = Debug.register_debug_module "Encapsulation"
let debug_msg = Debug.debug_msg debug_id
let debug_lmsg = Debug.debug_lmsg debug_id

type encapStatus = EncapOnly | EncapPlus | NotEncap

let string_of_encap (encap : encapStatus) : string =
  match encap with
    | EncapOnly -> "encap"
    | EncapPlus -> "encap+"
    | NotEncap -> "not encapsulated"

let is_primitive_type (tf : typeForm) : bool =
  match tf with
    | TypeApp(TypeInt, [])
    | TypeApp(TypeBool, []) -> true
    | _ -> false

let is_primitive_field (vd : var_decl) : bool =
  let tf = vd.vd_type in
  let result = match tf with
    | TypeApp(TypeArray, [(TypeApp(TypeObject,[])); field_tf]) -> 
        is_primitive_type field_tf
    | _ -> false in
  let msg = if result then "" else "not " in
    debug_lmsg 1 ( fun () -> MlPrintForm.string_of_type tf
                             ^ " is " ^ msg ^ "primitive.\n");
    result

(** Returns true for variables that have primitive type. **)
let has_primitive_type (vd : var_decl) : bool =
  is_primitive_type vd.vd_type

let is_global_vd (vd : var_decl) : bool =
  not vd.vd_field

let is_primitive_global_vd (vd : var_decl) : bool =
  (has_primitive_type vd) && (is_global_vd vd)

(** Returns the declared encapsulation status for a variable. **)
let decl_encap_vd (vd : var_decl) : encapStatus =
  let encap, eplus = vd.vd_encap in
    if encap then
      (if eplus then EncapPlus else EncapOnly)
    else
      NotEncap

let encap_or_primitive_fd (vd : var_decl) : encapStatus =
  if (is_primitive_field vd) then
    (** References to primitive types cannot escape, so they are
        always encapsulated. **)
    EncapOnly
  else
    decl_encap_vd vd

let encap_or_primitive_vd (vd : var_decl) : encapStatus =
  if (has_primitive_type vd) then
    (** References to primitive types cannot escape, so they are
        always encapsulated. **)
    EncapOnly
  else
    decl_encap_vd vd

let not_this (id : ident) : bool =
  not (id = this_id)

(** The analysis result is currently the list of local variables in
    the method that are guaranteed to refer only to encapsulated
    (private) data, plus a list of local variables that refer to
    arrays that are themselves private *and* contain only private
    data. **)
type aresult = {
  ar_encap : ident list;
  ar_eplus : ident list; (** ar_eplus is a subset of ar_encap **)
}

let empty_aresult = { ar_encap = []; ar_eplus = []; }

let string_of_id_list (ids : ident list) : string =
  "[" ^ (String.concat " " ids) ^ "]"

let debug_print_aresult (comment : string) (encap : aresult) : unit =
  let msg = "\n\n" ^ comment ^ "\n" ^ 
    "{ ar_encap = " ^ (string_of_id_list encap.ar_encap) ^ "\n" ^
    "  ar_eplus = " ^ (string_of_id_list encap.ar_eplus) ^ " }" ^ "\n\n" in
    debug_lmsg 1 (fun () -> msg)

let is_encap (encap : encapStatus) : bool =
  match encap with
    | EncapOnly | EncapPlus -> true
    | NotEncap -> false

let is_decl_encap_vd (vd : var_decl) : bool =
  is_encap (decl_encap_vd vd)

let is_encap_or_prim_vd (vd : var_decl) : bool =
  is_encap (encap_or_primitive_vd vd)

let not_encap (encap : encapStatus) : bool =
  not (is_encap encap)

(** Returns the encapsulation status for id. **)
let encap_status (encap : aresult) (id : ident) : encapStatus =
  if (id = this_id) then
    EncapOnly
  else if (List.mem id encap.ar_encap) then
    (if (List.mem id encap.ar_eplus) then
       EncapPlus
     else 
       EncapOnly)
  else
    NotEncap

let set_unencap 
    (eids : aresult) 
    (ar : aresult) 
    (id : ident) : aresult =
  if (not_this id) then
    if (List.mem id eids.ar_encap) then
      (** id is a parameter that has been declared encapsulated **)
      failwith ("\nEncapsulated parameter " ^ id ^ " may escape.\n\n")
    else
      { ar_encap = set_remove id ar.ar_encap;
        ar_eplus = set_remove id ar.ar_eplus; }
  else 
    (print_string ("\nEncapsulation.set_unencap: " ^ id ^ "\n\n"); ar)

let set_uneplus
    (eids : aresult)
    (ar : aresult) 
    (id : ident) : aresult =
  if (List.mem id eids.ar_eplus) then
    (** id is a parameter that has been declared encap+ **)
    failwith ("\nencap+ parameter " ^ id ^ " may escape.\n\n")
  else
    { ar_encap = ar.ar_encap;
      ar_eplus = set_remove id ar.ar_eplus; }

(** is e0 < e1? **)
let lt_encap_status (e0 : encapStatus) (e1 : encapStatus) : bool =
  match e0 with
    | EncapPlus -> false
    | EncapOnly -> (e1 = EncapPlus)
    | NotEncap -> (e1 = EncapOnly) || (e1 = EncapPlus)

let min_encap_status (e0 : encapStatus) (e1 : encapStatus) : encapStatus =
  if (lt_encap_status e0 e1) then e0 else e1

let make_ar (encap : ident list) : aresult =
  { ar_encap = encap; ar_eplus = [] }

let ar_unchanged (ar0 : aresult) (ar1 : aresult) =
  ((List.length ar0.ar_encap) = (List.length ar1.ar_encap)) &&
    ((List.length ar0.ar_eplus) = (List.length ar1.ar_eplus))

let is_primitive_global (prog : program) (id : ident) : bool =
  match Util.split_by "." id with
    | [mname;var] -> 
        (match find_sm mname prog with
           | Some sm -> 
               (match find_var id sm.sm_spec_vars with
                  | Some vd -> is_primitive_global_vd vd
                  | None -> 
                      (match find_im mname prog with
                         | Some im -> 
                             (match find_var id im.im_vars with
                                | Some vd -> is_primitive_global_vd vd
                                | None -> false)
                         | None -> false))
           | None -> false)
    | _ -> false

let is_encap_or_pglobal
    (prog : program) (encap : aresult) (id : ident) : encapStatus =
  if is_primitive_global prog id then
    EncapOnly
  else
    encap_status encap id

(** Returns the declared encapsulation status of the field. **)
let decl_encap_of_field (prog : program) (fld : ident) : encapStatus =
  let vdo = vd_of_field prog fld in
    match vdo with
      | Some vd -> decl_encap_vd vd
      | None -> NotEncap

(** Returns the encapsulation status of the field based on its
    declaration or EncapOnly if it is a primitive field. **)
let encap_or_prim_field (prog : program) (fld : ident) : encapStatus =
  let vdo = vd_of_field prog fld in
    match vdo with
      | Some vd -> encap_or_primitive_fd vd
      | None -> NotEncap

(** For these operations, the operands and target do not affect each
    other's encapsulation status, but the operands may involve field
    dereferences or other operations that are relevant to the
    analysis.  **)
let encap_neutral_op (op : constValue) : bool =
  match op with
    | Eq | Elem
    | Lt | Gt | LtEq | GtEq 
    | UMinus | Plus | Minus | Mult | Div | Mod -> true
    | _ -> false

let logical_connective (op : constValue) : bool =
  match op with
    | Or | And | Not | Impl | Iff -> true
    | _ -> false

let is_const (cv : constValue) : bool =
  match cv with
    | IntConst _ | BoolConst _ | NullConst 
    | EmptysetConst -> true
    | _ -> false

let hidden_set_name_len = String.length Jast.hidden_set_name

let is_hidden_set (id : ident) : bool =
  let sublen = (String.length id) - hidden_set_name_len in
    if (0 < sublen) then
      let tl = String.sub id sublen hidden_set_name_len in
        (tl = Jast.hidden_set_name)
    else false

(** Check that encapsulated fields are only accessed through encapsulated objects. **)
let check_encap_field_obj 
    (prog : program) 
    (im : impl_module) 
    (encap : aresult) 
    (obj : ident) 
    (field : ident) : unit =
  let d_encap = decl_encap_of_field prog field in
  let o_encap = encap_status encap obj in
    if (is_encap d_encap) && (not_encap o_encap) then
      (** It is a violation of encapsulation to access an encapsulated
          field through an unencapsulated object. We check the
          declared status of the field because a field may be
          encapsulated because it is primitive, in which case it would
          be ok to dereference it even if the target object is not
          encapsulated. **)
      failwith ("Field " ^ field ^ " is declared " ^ (string_of_encap d_encap) ^ 
                  " but is accessed through unencapsulated object " ^ obj ^ ".\n")

(** Transfer function for field deference and assignment.
      Field dereference: id = obj.field 
      Field assignment : obj.field = id **)
let field_transfer_function 
    (prog : program)
    (im : impl_module)
    (eids: aresult) 
    (encap : aresult)
    (obj : ident)
    (field : ident)
    (id : ident) : aresult =
  let f_encap = decl_encap_of_field prog field in
  let i_encap = is_encap_or_pglobal prog encap id in
    debug_lmsg 1 (fun () -> "Field " ^ field ^ " is " ^ (string_of_encap f_encap) ^ "\n");
    debug_lmsg 1 (fun () -> "Identifier " ^ id ^ " is " ^ (string_of_encap i_encap) ^ "\n");
    check_encap_field_obj prog im encap obj field;
    match f_encap with
      | EncapPlus ->
          if not (i_encap = EncapPlus) then
            failwith ("Field " ^ field ^ " is declared encap+ but " ^ 
                        id ^ " is " ^ (string_of_encap i_encap) ^ ".\n");
          encap
      | EncapOnly ->
          if (not_encap i_encap) then
            failwith ("Field " ^ field ^ " is declared encap but " ^
                         id ^ " is " ^ (string_of_encap i_encap) ^ ".\n");
          (** downgrade id (in case it is encap+) **)
          set_uneplus eids encap id
      | NotEncap ->
          let ep = encap_or_prim_field prog field in
            if (not_encap ep) then
              set_unencap eids encap id
            else
              set_uneplus eids encap id

(** Transfer function for array read and write.
    Array read:  id = arr[i]
    Array write: arr[i] = id **)
let array_transfer_function 
    (prog : program) (eids: aresult) (encap : aresult) (arrName : ident) (id : ident) : aresult =
  let a_encap = encap_status encap arrName in
  let i_encap = is_encap_or_pglobal prog encap id in
    match a_encap with
      | EncapPlus ->
          if (is_encap i_encap) then
            (** Content is also encapsulated. **)
            encap
          else
            (** Content not encapsulated. **)
            set_uneplus eids encap arrName
      | _ ->
          (** Array contents not encapsulated. **)
          set_unencap eids encap id

(** Update encapsulation result appropriately for the given operand. **)
let check_operand
    (prog : program) 
    (im : impl_module) 
    (eids : aresult)
    (encap : aresult)
    (f : form) : aresult =
  match f with
    | Const cv when (is_const cv) -> encap
    | Var id -> encap
    | _ -> 
        print_string 
	  ("\nWARNING: Encapsulation.check_operand: Unmatched operand [" ^
             (MlPrintForm.string_of_form f) ^ "]\n\n");
	encap

let copy_transfer_function
    (prog : program)
    (eids : aresult)
    (encap : aresult)
    (lhs : ident)
    (rhs : ident) : aresult =
  let lhs_encap = is_encap_or_pglobal prog encap lhs in
  let rhs_encap = is_encap_or_pglobal prog encap rhs in
  let set_unencap_int = set_unencap eids encap in
  let set_uneplus_int = set_uneplus eids encap in
    match lhs_encap with
      | EncapPlus ->
          (match rhs_encap with
             | EncapPlus -> encap
             | EncapOnly -> set_uneplus_int lhs
             | NotEncap -> set_unencap_int lhs)
      | EncapOnly ->
          (match rhs_encap with
             | EncapPlus -> set_uneplus_int rhs
             | EncapOnly -> encap
             | NotEncap -> set_unencap_int lhs)
      | NotEncap ->
          set_unencap_int rhs

(*
let encap_of_form 
    (prog : program) 
    (im : impl_module) 
    (eids : aresult) 
    (encap : aresult) 
    (f : form) : encapStatus =
  match f with
    | Var id -> encap_status encap id
    | App(Const ArrayRead, [(Var arrState); (Var arrName); f0]) 
        when (arrState = arrayStateId) ->
        let encap0 = check_operand prog im eids encap f0 in
        let arr_encap = encap_status encap0 arrName in
          (match arr_encap with
             | EncapPlus -> EncapOnly
             | _ -> NotEncap)
    | _ ->
        print_string ("Unmatched formula in encap_of_form:\n" ^ 
			(PrintForm.string_of_form f) ^ "\n");
        NotEncap
*)

let set_uneplus_of_form
    (prog : program) 
    (im : impl_module) 
    (eids : aresult) 
    (encap : aresult) 
    (f : form) : aresult =
  match f with
    | Var id -> set_uneplus eids encap id
    | App(Const ArrayRead, [(Var arrState); (Var arrName); f0])
        when (arrState = arrayStateId) ->
        (** The result of the read is not 'encap+', but this doesn't
            change the encapsulation of the containing array. **)
        check_operand prog im eids encap f0
    | _ ->
        failwith ("Unmatched formula in set_uneplus_of_form:\n" ^ 
		    (PrintForm.string_of_form f) ^ "\n")

let rec set_unencap_of_form
    (prog : program) 
    (im : impl_module) 
    (eids : aresult) 
    (encap : aresult) 
    (f : form) : aresult =
  match f with
    | Const _ -> encap
    | Var id -> set_unencap eids encap id
    | App(Const ArrayRead, [(Var arrState); (Var arrName); f0])
        when (arrState = arrayStateId) ->
        (** The result of the read is not 'encap', which means that
            the containing array cannot be 'encap+'. **)
        let encap0 = check_operand prog im eids encap f0 in
          set_uneplus eids encap0 arrName
    | App(Const Tuple, fs) ->
        List.fold_left (set_unencap_of_form prog im eids) encap fs
    | App(Const op, fs) when (logical_connective op) ->
        List.fold_left (set_unencap_of_form prog im eids) encap fs
    | App(Const op, fs) when (encap_neutral_op op) ->
        List.fold_left (set_unencap_of_form prog im eids) encap fs
    | Binder(Exists, _, f0) ->
        set_unencap_of_form prog im eids encap f0

	  (** TODO: double-check actions below **)
    | App(Var "rtrancl_pt", fs) ->
        List.fold_left (set_unencap_of_form prog im eids) encap fs
    | Binder(Lambda, _, f0) ->
        set_unencap_of_form prog im eids encap f0
    | App(Const FieldRead, fs) ->
        List.fold_left (set_unencap_of_form prog im eids) encap fs
    | _ ->
        failwith ("Unmatched formula in set_unencap_of_form:\n" ^ 
		    (MlPrintForm.string_of_form f) ^ "\n")

let finite_set_transfer_function
    (prog : program)
    (im : impl_module)
    (eids : aresult)
    (lhs : ident) 
    (encap : aresult) 
    (f : form) : aresult =
  let lhs_encap = encap_status encap lhs in
    match lhs_encap with
      | EncapPlus -> set_uneplus_of_form prog im eids encap f
      | _ -> set_unencap_of_form prog im eids encap f
          
(** The transfer functions for assignments, which encompasses most of
    the important transfer functions. **)
let rec analyze_assign 
    (prog : program)
    (im : impl_module)
    (eids : aresult)
    (id : ident)
    (encap : aresult)
    (tf : form) : aresult =
  debug_lmsg 1 (fun () -> "Analyzing assignment to: " ^ (PrintForm.string_of_form tf) ^ "\n");
  let handle_unknown (f : form) : aresult =
    (** For formulas we know nothing about, conservatively
        assume that all variables may escape. TODO: We don't
        need to be that conservative, because primitive types
        can't be leaked, but in order to save those, we would
        need to have the type information for the variables. **)
    print_string ("\nEncapsulation.analyze_assign: Unmatched rhs in ["
                  ^ id ^ " = " ^ (MlPrintForm.string_of_form f) ^ "]\n\n");
    empty_aresult in
  let f = remove_comments_and_typedform tf in
    match f with
      | Const cv when (is_const cv) -> encap
      | Var id0 -> 
          copy_transfer_function prog eids encap id id0
      | App(Const FieldRead, [(Var field); (Var obj)]) ->
          field_transfer_function prog im eids encap obj field id
      | App(Const FieldWrite, [(Var field); (Var obj); (Var id)]) ->
          field_transfer_function prog im eids encap obj field id
      | App(Const FieldWrite, [(Var field); (Var obj); (Const cv)]) 
          when (is_const cv) -> 
          (** x.f = <const> **)
          (** Check that the field access is valid. **)
          check_encap_field_obj prog im encap obj field;
            encap
      | App(Const FieldWrite, [(Var field); (Var obj); f0]) ->
          (** This case should only occur for assignments of ghost specvars. **)
          (match f0 with
             | _ -> handle_unknown f)
      | App(Const ArrayRead, [(Var arrState); (Var arrName); f0])
          when (arrState = arrayStateId) ->
          let encap0 = check_operand prog im eids encap f0 in
            array_transfer_function prog eids encap0 arrName id
      | App(Const ArrayWrite, [(Var arrState); (Var arrName); f0; (Var id0)]) 
          when (id = arrayStateId) && (arrState = arrayStateId) ->
          let encap0 = check_operand prog im eids encap f0 in
            array_transfer_function prog eids encap0 arrName id0
      | App(Const ArrayWrite, [(Var arrState); (Var _); f0; (Const cv)])
          when (id = arrayStateId) && (arrState = arrayStateId) && (is_const cv) ->
          check_operand prog im eids encap f0
      | App(Const Cup, 
            [(Var id0); App(Const FiniteSetConst, [Var _])])
          when (id = all_alloc_objs) && (id0 = all_alloc_objs) ->
          (** Object_alloc = Object_alloc Un { _ } **)
          encap
      | App(Const Cup, [(Var hsn); App(Const FiniteSetConst, [Var _])])
          when ((is_hidden_set hsn) && (is_hidden_set id)) ->
          (** <Class>_hidden = <Class>_hidden Un { _ } **)
          encap
      | App(Const Diff, fs) (** Conservatively treat as union. **)
      | App(Const Cap, fs)  (** Conservatively treat as union. **)
      | App(Const Cup, fs) ->
          (** The contents of the union'd sets flow into the lhs. **)
          List.fold_left (analyze_assign prog im eids id) encap fs
      | App(Const FiniteSetConst, fs) ->
          (** This is similar to an array write. The handle to the set
              does not escape, but the contents may change the
              encapsulation properties of the lhs. **)
          List.fold_left (finite_set_transfer_function prog im eids id) encap fs
      | App(Const op, fs) when (logical_connective op) ->
          (** With logical connectives, the lhs and rhs don't
              interchange encapsulation information, since they are of
              boolean type, but the subformulas may include accesses that
              are important, so we want to recursively descend them. **)
          List.fold_left (analyze_assign prog im eids id) encap fs
      | App(Const op, fs) when (encap_neutral_op op) ->
          List.fold_left (check_operand prog im eids) encap fs
      | Binder(Comprehension, _, f0) ->
          (** The constraints on the set could be arbitrarily
              complicated, so conservatively assume that all referenced
              variables are leaked. **)
          let encap0 = set_unencap eids encap id in
            set_unencap_of_form prog im eids encap0 f0
      | _ -> handle_unknown f

let analyze_arg 
    (eids : aresult) (encap : aresult) (param : var_decl) (arg : form) : aresult =
  match arg with
    | Var id ->
        (let p_encap = decl_encap_vd param in
         let a_encap = encap_status encap id in
           match p_encap with
             | EncapPlus ->
                 if not (a_encap = EncapPlus) then
                   failwith ("Parameter " ^ param.vd_name ^ 
                               " is declared encap+ but argument " ^ id ^ 
                               " is " ^ (string_of_encap a_encap) ^ ".\n")
                 else
                   encap
             | EncapOnly ->
                 if (not_encap a_encap) then
                   failwith ("Parameter " ^ param.vd_name ^ 
                               " is declared encap but argument " ^ id ^ 
                               " is " ^ (string_of_encap a_encap) ^ ".\n")
                 else
                   set_uneplus eids encap id
             | NotEncap ->
                 (** Even if the parameter is not declared as encapsulated, 
                     it may be encapsulated because it is primitive. **)
                 if (has_primitive_type param) then
                   set_uneplus eids encap id
                 else 
                   set_unencap eids encap id)
    | Const _ -> encap
    | _ ->
        print_string ("analyze_arg: unexpected argument" ^ (PrintForm.string_of_form arg) ^ "\n");
        empty_aresult

let analyze_args (pc : proc_call) (eids : aresult) (encap : aresult) : aresult =
  let args = pc.callee_args in
  let callee_hdr = get_callee_hdr pc in
  let params = callee_hdr.p_formals in
    if (List.length params = 0) then
      encap
    else
      let p0 = name_of_vd (List.hd params) in
      let params0, args0 = 
        if (p0 = this_id) then
          match List.hd args with
            | Var a0 when (a0 = this_id) ->
                ((List.tl params), (List.tl args))
            | _ -> (params, args)
        else
          (params, args) in
        List.fold_left2 (analyze_arg eids) encap params0 args0

(** The actual transfer functions of the encapsulation analysis. **)
let rec analyze_command 
    (prog : program) 
    (im : impl_module)
    (eids : aresult)
    (encap : aresult) 
    (c : command) : aresult =
  let analyze = analyze_command prog im eids in
  let set_unencap_int = set_unencap eids in
    try
      match c with
        | Basic { bcell_cmd = bc } ->
            let result =
            (match bc with
               | VarAssign { assign_lhs = lhs; assign_rhs = rhs; } ->
                   analyze_assign prog im eids lhs encap rhs
               | ProcCall pc ->
                   let encap0 = analyze_args pc eids encap in
                     (match pc.callee_res with
                        | Some id ->
                            let callee_hdr = get_callee_hdr pc in
                              if (is_primitive_type callee_hdr.p_restype) then
                                encap0
                              else
                                set_unencap_int encap0 id 
                        | None -> encap0)
               | _ -> encap) in
              debug_print_aresult (PrintAst.pr_command c) result; result
        | Seq cl | Choice cl -> List.fold_left analyze encap cl
        | If {if_then = it; if_else = ie} ->
            analyze (analyze encap it) ie
        | Loop {loop_prebody = pre; loop_test = test; loop_postbody = post} ->
            let encap0 = analyze encap pre in
            let test0 = remove_comments_and_typedform test in
            let encap1 = check_operand prog im eids encap0 test0 in
              analyze encap1 post
        | Return { return_exp = re } ->
            (match re with
               | None -> encap
               | Some f -> 
                   match f with
                     | TypedForm((Var id), tf) ->
                         if (is_primitive_type tf) then
                           (** we know we are returning a primitive.
                               the local variable does not escape. **)
                           encap
                         else
                           set_unencap_int encap id
                     | Var id ->
                         set_unencap_int encap id
                     | TypedForm((Const cv), _) 
                     | Const cv when (is_const cv) -> encap
                     | _ -> 
                         failwith ("\nanalyze_command: unmatched return " ^
                                     (PrintAst.pr_command c) ^ "\n"))
        | _ -> encap
    with Failure msg -> 
      print_string (msg ^ "In command: " ^ (PrintAst.pr_command c) ^ "\n");
      failwith ""

let check_encap_params (prog : program) (im : impl_module) (p : proc_def) : unit =
  let phdr = p.p_header in
  let decl_encap_params = List.filter is_decl_encap_vd phdr.p_formals in
    if (0 < (List.length decl_encap_params)) && phdr.p_public then
      let id = name_of_vd (List.hd decl_encap_params) in
        (** Public methods should not have encapsulated arguments. **)
        failwith ("Public method " ^ phdr.p_name ^ 
                    " takes encapsulated parameter " ^ id)

let mk_eids (vds : var_decl list) : aresult =
  let rec mk_eids_int (eids : aresult) (todo : var_decl list) : aresult =
    match todo with
      | [] -> eids
      | vd :: rest ->
          let id = name_of_vd vd in
          let d_encap = decl_encap_vd vd in
          let eids0 = match d_encap with
            | EncapPlus -> { ar_encap = id :: eids.ar_encap;
                             ar_eplus = id :: eids.ar_eplus; }
            | EncapOnly -> { ar_encap = id :: eids.ar_encap;
                             ar_eplus = eids.ar_eplus; }
            | NotEncap -> failwith ("Can't happen") in
            mk_eids_int eids0 rest
  in
    mk_eids_int { ar_encap = []; ar_eplus = []; } vds

(** Runs encapsulation analysis, returning the analysis result. **)
let analyze_method
    (prog : program) 
    (im : impl_module) 
    (p : proc_def) : aresult =
  check_encap_params prog im p;
  let phdr = p.p_header in
  let vds = List.filter is_encap_or_prim_vd phdr.p_formals in
  let denc_vds, prim_vds = List.partition is_decl_encap_vd vds in
  let denc_ar = mk_eids denc_vds in
  let denc_ids  = List.map name_of_vd denc_vds in
  let prim_ids  = List.map name_of_vd prim_vds in
  let local_ids = List.map name_of_vd p.p_locals in
  let ar = make_ar (local_ids @ denc_ids @ prim_ids) in
  let rec analyze_to_fp (encap : aresult) : aresult =
    debug_print_aresult "Analysis Result:" encap;
    try
      let encap0 = analyze_command prog im denc_ar encap p.p_body in 
        if (ar_unchanged encap0 encap) then
          encap0
        else
          analyze_to_fp encap0
    with Failure msg ->
      print_string msg; failwith ""
  in
    debug_lmsg 1 (fun () -> "*** " ^ im.im_name ^ "." ^ p.p_header.p_name ^ " ***");
    debug_print_aresult "Declared Encapsulated" denc_ar;
    debug_lmsg 1 (fun () -> "local_ids = " ^ (string_of_id_list local_ids) ^ "\n");
    debug_lmsg 1 (fun () -> "prim_ids  = " ^ (string_of_id_list prim_ids) ^ "\n");
    analyze_to_fp ar

let check_encap_assign 
    (prog : program) (p : proc_def) (ac : assign_command) (encap : aresult) : unit =
  let f = remove_comments_and_typedform ac.assign_rhs in
    match f with
      | App(Const FieldWrite, [(Var _); (Var obj); _]) ->
          (** check that the target object is private data **)
          let o_encap = encap_status encap obj in
            if not (is_encap o_encap) then
              let msg = "\n\nEncapsulated method " ^ p.p_header.p_name ^ 
                " modifies unencapsulated obj.\n\n" in
                failwith msg
      | App(Const ArrayWrite, [(Var arrState); (Var arrName); _; _])
          when (ac.assign_lhs = arrayStateId) && (arrState = arrayStateId) ->
          (** check that the target object is private data **)
          let a_encap = encap_status encap arrName in
            if not (is_encap a_encap) then
              let msg = "\n\nEncapsulated method " ^ p.p_header.p_name ^ 
                " modifies unencapsulated array.\n\n" in
                failwith msg
      | _ -> (** check that no writes of static fields are occurring **)
          let lhs = ac.assign_lhs in
          let globals = List.map (fun g -> g.global_name) prog.p_globals in
            if (List.mem lhs globals) then
              let msg = "\n\nEncapsulated method " ^ p.p_header.p_name ^ 
                " modifies static field " ^ lhs ^ ".\n\n" in
                failwith msg

let check_encap_proc_call (p : proc_def) (pc : proc_call) (encap : aresult) : unit =
  let callee_hdr = get_callee_hdr pc in
    (if not (callee_hdr.p_encap) then
       let msg = "\n\nEncapsulated method " ^ p.p_header.p_name ^ 
         " calls unencapsulated method " ^ callee_hdr.p_name ^ ".\n\n" in
         failwith msg);
    (** For now, only allow calls on receiver. **)
    let args = pc.callee_args in
    let params = callee_hdr.p_formals in
      if (List.length params = 0) then
        ()
      else
        let p0 = name_of_vd (List.hd params) in
        let f0 = List.hd args in 
          match f0 with
            | Var a0 when (a0 = this_id) && (p0 = this_id) -> ()
            | _ ->
                let msg = "\n\nEncapsulated method " ^ p.p_header.p_name ^ 
                  " calls " ^ callee_hdr.p_name ^ " on " ^ 
                  (PrintForm.string_of_form f0) ^ ".\n\n" in
                  failwith msg
                    
let rec check_encap_command 
    (prog : program) 
    (im : impl_module) 
    (p : proc_def) 
    (encap : aresult) 
    (c : command) : unit =
  let check_encap_command_int = check_encap_command prog im p encap in
  try
    match c with
      | Basic { bcell_cmd = bc } -> 
          (match bc with
             | VarAssign ac -> check_encap_assign prog p ac encap
             | Alloc { alloc_type = atype } ->
                 if atype = im.im_name then
                   let msg = "\n\nEncapsulated method " ^ p.p_header.p_name ^ 
                     " allocates objects of type " ^ atype ^ "."in
                     failwith msg
             | ProcCall pc -> check_encap_proc_call p pc encap
             | _ -> ())
      | Seq cl | Choice cl -> List.iter check_encap_command_int cl
      | If { if_then = it; if_else = ie } ->
          check_encap_command_int it;
          check_encap_command_int ie
      | Loop { loop_prebody = pre; loop_postbody = post } ->
          check_encap_command_int pre;
          check_encap_command_int post
      | _ -> ()
  with Failure msg ->
    print_string (msg ^ "\nIn command: " ^ (PrintAst.pr_command c) ^ "\n");
    failwith ""
      
(** Checks whether an analyzed method modifies only encapsulated data. **)
let check_encap_method 
    (prog : program) (im : impl_module) (p : proc_def) (encap : aresult) : unit =
  try
    check_encap_command prog im p encap p.p_body
  with Failure msg ->
    print_string msg; Util.fail msg

let handle_method 
    (prog : program) 
    (im : impl_module) 
    (p : proc_def) : unit =
  let encap = analyze_method prog im p in
    if p.p_header.p_encap then
      check_encap_method prog im p encap

let rec check_encap_form (f : form) : bool =
  debug_lmsg 1 (fun () -> "check_encap_form: " ^ (PrintForm.string_of_form f)
                          ^ "\n\n");
  match f with
    | Const _ -> true
    | Var id -> not (id = all_alloc_objs) && not (is_hidden_set id)
    | App(Const FieldRead, [_; (Var obj)]) -> obj = this_id
    | App(_, fs) -> List.for_all check_encap_form fs
    | Binder(_, _, f0) -> check_encap_form f0
    | TypedForm(f0, _) -> check_encap_form f0

let is_mapping_of_impl (im : impl_module) (m : mapping) : bool =
  m.map_impl = im

let is_mapping_of_spec (sm : spec_module) (m : mapping) : bool =
  m.map_spec = sm

let specvar_defs_of_mapping (m : mapping) : specvar_def list =
  m.map_abst

let im_must_find_specvar_def (prog : program) (im : impl_module) (vd : var_decl) : specvar_def =
  let mappings = List.filter (is_mapping_of_impl im) prog.p_maps in
  let mapping_svds = List.flatten (List.map specvar_defs_of_mapping mappings) in
  let smo = find_sm im.im_name prog in
  let sm_svds = 
    match smo with
      | Some sm -> sm.sm_constdefs @ sm.sm_vardefs
      | None -> [] in
  let im_svds = im.im_vardefs @ im.im_constdefs in
  let svds = mapping_svds @ sm_svds @ im_svds in
  let id = name_of_vd vd in
    try
      let f = List.assoc id svds in
        (id, f)
    with Not_found ->
      Util.fail ("im_must_find_specvar_def: could not find definition for "
                 ^ id ^ "\n")
        
let sm_must_find_specvar_def (prog : program) (sm : spec_module) (vd : var_decl) : specvar_def =
  let mappings = List.filter (is_mapping_of_spec sm) prog.p_maps in
  let mapping_svds = List.flatten (List.map specvar_defs_of_mapping mappings) in
  let imo = find_im sm.sm_name prog in
  let im_svds = 
    match imo with
      | Some im -> im.im_constdefs @ im.im_vardefs
      | None -> [] in
  let sm_svds = sm.sm_vardefs @ sm.sm_constdefs in
  let svds = mapping_svds @ sm_svds @ im_svds in
  let id = name_of_vd vd in
    try
      let f = List.assoc id svds in
        (id, f)
    with Not_found ->
      Util.fail ("sm_must_find_specvar_def: could not find definition for "
                 ^ id ^ "\n")
        
let remove_lambda (f : form) : form =
  match f with
    | Binder(Lambda, [(id, _)], f0) when (id = this_id) -> f0
    | _ ->
        Util.fail ("remove_lambda: " ^ (PrintForm.string_of_form f) ^ "\n")

let check_im_var_decl (prog : program) (im : impl_module) (vd : var_decl) : unit =
  let vd_encap = decl_encap_vd vd in
  let vd_owner = 
    match vd.vd_owner with 
      | Some owner -> owner 
      | None -> im.im_name in
    if (is_encap vd_encap) then
      match vd.vd_jtype with
        | Some jtype -> 
            if (jtype = vd_owner) then
              failwith ("Field " ^ vd.vd_name ^ " cannot be declared "
                        ^ (string_of_encap vd_encap) ^ " because it has the \
                           same type as the owning class " ^ vd_owner ^ ".\n")
        | None -> ();
    if (is_encap vd_encap) && vd.vd_abstract && (not vd.vd_ghost) then
      (** abstract non-ghost variable declared encapsulated:
          need to check that the definition is valid **)
      let (id, f) = im_must_find_specvar_def prog im vd in
      let f0 = if vd.vd_field then remove_lambda f else f in
        if not (check_encap_form f0) then
          Util.fail ("check_var_decl: specvar "
                     ^ id ^ " may not be encapsulated.\n")

let check_sm_var_decl (prog : program) (sm : spec_module) (vd : var_decl) : unit =
  let vd_encap = decl_encap_vd vd in
    if (is_encap vd_encap) && vd.vd_abstract && (not vd.vd_ghost) then
      (** abstract non-ghost variable declared encapsulated:
          need to check that the definition is valid **)
      let (id, f) = sm_must_find_specvar_def prog sm vd in
      let f0 = if vd.vd_field then remove_lambda f else f in
        if not (check_encap_form f0) then
          Util.fail ("check_var_decl: specvar "
                     ^ id ^ " may not be encapsulated.\n")

let analyze_vardefs (prog : program) (vds : specvar_def list) : unit =
  debug_lmsg 1 (fun () -> PrintAst.pr_vardefs vds)

let analyze_module (prog : program) (im : impl_module) : unit =
  List.iter (handle_method prog im) im.im_procs;
  List.iter (check_im_var_decl prog im) im.im_vars;
  debug_lmsg 1 (fun () -> im.im_name ^ " *** vardefs ***\n");
  analyze_vardefs prog im.im_vardefs;
  debug_lmsg 1 (fun () -> im.im_name ^ " *** constdefs ***\n");
  analyze_vardefs prog im.im_constdefs

let analyze_spec (prog : program) (sm : spec_module) : unit =
  List.iter (check_sm_var_decl prog sm) sm.sm_spec_vars;
  debug_lmsg 1 (fun () -> sm.sm_name ^ " *** vardefs ***\n");
  analyze_vardefs prog sm.sm_vardefs;
  debug_lmsg 1 (fun () -> sm.sm_name ^ " *** constdefs ***\n");
  analyze_vardefs prog sm.sm_constdefs

let encapsulation_analysis (prog : program) : unit =
  debug_lmsg 1 (fun () -> "Starting encapsulation analysis.\n");
  let m = List.map (fun m -> m.map_abst) prog.p_maps in
    debug_lmsg 1 (fun () -> "*** mapping vardefs ***\n");
    List.iter (analyze_vardefs prog) m;
    List.iter (analyze_module prog) prog.p_impls;
    List.iter (analyze_spec prog) prog.p_specs;
    debug_lmsg 1 (fun () -> "Encapsulation analysis completed.\n")
