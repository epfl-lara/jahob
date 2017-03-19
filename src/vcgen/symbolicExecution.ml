
(******************************)
(***                        ***)
(***   Symbolic execution   ***)
(***                        ***)
(******************************)

(* WARNING: arrays cannot be aliased, they are always considered to be copies.
   For instance, if a = b, b[i] = r does not modifiy a. *)

(* TODO: Check that arrays are properly handled. *)

(* BUGS: look for XXX in the code *)

open Ast
open Form
open FormUtil
open Printf

(* {6 Debugging shorthands} *)
let debug_id = Debug.register_debug_module "SymbolicExecution"
let debug_msg : string -> unit = Debug.debug_msg debug_id
let debug_lmsg : int -> (unit -> string) -> unit = Debug.debug_lmsg debug_id
let debug_is_on : unit -> bool = fun () -> Debug.debug_is_on debug_id


(******************************)
(* {6 Special value handling} *)
(******************************)


let undef_prefix = "new_"
let unknown_prefix = "unknown_"
let init_prefix = "initial_"
let init id = mk_var (init_prefix ^ id)
let any id = mk_var (Util.fresh_name "any_value")
let mk_undef id = id, mk_var (undef_prefix ^ id)
let mk_unknown id = id, mk_var (unknown_prefix ^ id)

(* [is_cell arr cell] tests if [cell] is a cell of the array [arr]. *)
let is_cell arr cell = Scanf.sscanf cell "%s[%s]" (fun a i -> a = arr)

let is_defined = function
  | Var ident ->
      let length = String.length undef_prefix in
      not (String.length ident > length
           && String.sub ident 0 length = undef_prefix)
  | _ -> true


(*********************************************)
(* {6 Types and constant values definitions} *)
(*********************************************)


type variables =
    (Form.ident * Form.form) list * (Form.ident * Form.form list) list

type state = { values : (ident * form) list;      (* variables with values *)
               arrays : (ident * form list) list; (* arrays with dimensions *)
               path_condition : form list;
               verification_condition : form list;
               returned : bool } (* computation is over *)

(* Internal variables used by Jahob *)
let internal_vars =
  [all_alloc_objs; arrayName; result_var; Jast.hidden_set_name]

(* Same as [internal_defs] but in [state.values] form. *)
let internal_defs : variables = List.map (fun x -> x, init x) internal_vars,[]

(* Storage for global variable of the program. *)
let prog_vars : variables ref = ref internal_defs

(* Storage for the symbolic results of procedure. Used for procedure calls. *)
let exec_result : (ident, state list) Hashtbl.t = Hashtbl.create 23

(* Global reference to the program. *)
let prog : program ref = ref AstUtil.empty_prog


(****************************************)
(* {6 Manipulating and printing states} *)
(****************************************)


let add_path_condition cond state =
  {state with path_condition = cond :: state.path_condition}

let run action state =
  if state.returned then state else action state

(* XXX: should array be modified? *)
let apply_subst map state =
  {state with
     values = Util.map_snd (subst map) state.values;
     path_condition = List.map (subst map) state.path_condition;
     verification_condition = List.map (subst map) state.verification_condition}

(* [replace_VarValue ident value state] replaces the value of the variable
   [ident] by [value] in the state [state] and returns the resulting
   state. We assume that no two couples have same identifiers. *)
let replace_VarValue ident value state =
  let resolved_value = subst state.values value in
  try (* declared variable *)
    {state with
       values = (ident, resolved_value) :: Util.must_remove ident state.values}
  with Not_found -> (* non declared variable: undefined use of ident in value *)
    Util.warn ("SymbolicExec: variable " ^ ident ^ " assigned \
                  but not declared, assuming declaration.");
    {state with
        values = (ident, subst [mk_undef ident] resolved_value) :: state.values}

(* Same as [replace_VarValue] but for array assignment. Note: [array]
   is the name of the array and [ident] is the name of the cell. *)
let replace_ArrValue array ident value state =
  let resolved_value = subst state.values value in
    if List.mem_assoc array state.arrays
    then (* previously declared array, the cell may not be in state.values *)
      {state with
         values = (ident, resolved_value)
                  :: (List.remove_assoc ident state.values)}
    else
      begin (* non declared array: dimensions not known
               + undefined use of ident in value *)
        Util.warn ("SymbolicExecution: array " ^ array ^ " modified \
                    but not declared, assuming declaration.");
        {state with
           values = (ident, subst [mk_undef ident] resolved_value)
                    :: state.values;
           arrays = (array, []) :: state.arrays}
      end

(* Merge two states by adding or replacing new field values. *)
let merge_state state1 state2 =
  { values = Util.remove_dups_assoc (state1.values @ state2.values);
    arrays = Util.remove_dups_assoc (state1.arrays @ state2.arrays);
    path_condition = Util.union state1.path_condition state2.path_condition;
    verification_condition =
      Util.union state1.verification_condition state2.verification_condition;
    returned = state1.returned || state2.returned }

let purify_states predicate state_list =
  let purify_state state =
    {state with
       values = List.filter
        (fun (name, value) -> init name <> value && not (predicate name))
        state.values}
  in
    List.map purify_state state_list


let print_state impl_name state =

  (** printing the 'values' field *)
  printf "{values:  ";
  if (!Debug.debugOn || !Debug.debug_level > 0)
  then (* full printing with full name if debug is on *)
    List.iter
      (fun (name, value) -> printf "\n    %s = %s," name (PrintAst.pf value))
      state.values
  else (* remove 'tmp_*' variables and module prefix *)
    List.iter
      (fun (name, value) ->
         if not (Javajast.is_tmp name || init name = value)
         then
           printf "\n    %s = %s,"
             (Util.unqualify1 impl_name name)
             (PrintAst.pf value))
      state.values;

  (** printing the 'array' field *)
  printf "\b;\narrays:  ";
  List.iter
    (fun (name, dims) ->
       printf "\n    %s of size [%s],"
         name 
         (String.concat ", " (List.map PrintAst.pf dims)))
    state.arrays;

  (** printing the 'path_condition' field *)
  printf "\b;\npath condition:  ";
  List.iter
    (fun cond -> printf "\n    %s,"(PrintAst.pf cond))
    state.path_condition;
  printf "\b\n}\n"


let print_paths impl_name proc_name state_list =
  let number = List.length state_list in
    if number = 1
    then
      printf "\nModule %s, procedure %s: the only result of symbolic execution \
               is:\n" impl_name proc_name
    else
      printf "\nModule %s, procedure %s: the %d results of symbolic execution \
              are:\n" impl_name proc_name number;
    List.iter (print_state impl_name) state_list

let show_vars (values, arrays) =
  "{values:\n"
  ^ String.concat ",\n"
      (List.map
         (fun (name, value) ->
            "    " ^ name ^ " = " ^ (PrintForm.string_of_form value))
         values)
  ^ ";\narrays:\n"
  ^ String.concat ",\n"
      (List.map
         (fun (name, dims) ->
            "    " ^ name ^ " of size [" 
            ^ (String.concat ", " (List.map PrintAst.pf dims)) ^ "]")
         arrays)
  ^ "}\n"


let show_state pad state =

  (** showing the field values *)
  pad ^ "{values:\n"
  ^ pad ^ "    " ^ (String.concat (",\n" ^ pad ^ "    ")
                      (List.map
                         (fun (name, value) ->
                            "    " ^ name ^ " = " ^ (PrintAst.pf value))
                         state.values))
     
  (** showing the 'array' field *)
  ^ ";\n" ^ pad ^ "arrays:\n"
  ^ pad ^ "    " ^ (String.concat (",\n" ^ pad)
                      (List.map
                         (fun (name, dims) ->
                            "    " ^ name ^ " of size [" 
                            ^ (String.concat ", " (List.map PrintAst.pf dims))
                            ^ "]")
                         state.arrays))

  (** showing the field condition_path *)
  ^ ";\n" ^ pad ^ "path condition:\n"
  ^ pad ^ "    " ^ String.concat (",\n" ^ pad ^ "    ")
                     (List.map PrintAst.pf state.path_condition)

  (** showing the field verification_condition *)
  ^ ";\n" ^ pad ^ "verification condition:\n"
  ^ pad ^ "    " ^ String.concat (",\n" ^ pad ^ "    ")
                     (List.map PrintAst.pf state.verification_condition)
  ^ if state.returned
    then ";\n" ^ pad ^ "return statement encountered.\n"
    else ";\n" ^ pad ^ "no return statement encountered.\n"
  ^ pad ^ "}\n"


(***************************)
(** {6 Symbolic execution} *)
(***************************)


(** {3 for basic operations} *) 


let exec_Skip (state : state) =
  debug_lmsg 3 (fun () -> "executing a 'skip' command\n");
  state

let exec_Hint (hint : hint) (state : state) =
  debug_lmsg 3 (fun () -> "executing a 'hint' command\n");
  state

let exec_VarAssign assign state =
  if assign.assign_lhs = arrayStateId
  then
    begin  (* array assignment *)
      debug_lmsg 3 (fun () -> "executing an array assignment:\n"
                              ^ PrintAst.pr_var_assign assign);
      debug_lmsg 4 (fun () -> "state before assignment:\n"
                              ^ show_state "    " state);
      match assign.assign_rhs with
        | TypedForm (App (Const ArrayWrite, [a; arrObj; index; v]), _)
        | App (Const ArrayWrite, [a; arrObj; index; v]) ->
            if a <> arrayStateVar 
              && a <> Var (arrayName ^ "_" ^ shortArrayStateId)
            then Util.warn ("exec_VarAssign: first argument of ArrayWrite '"
                            ^ (PrintAst.pf assign.assign_rhs)
                            ^ "' (" ^ PrintAst.pf a
                            ^ ") is not arrayStateId (with '.' or '_')");
            let array,ident =
              match arrObj with
                | TypedForm (Var ar, _)
                | Var ar -> ar,
                    sprintf "%s[%s]" ar (PrintAst.pf (subst state.values index))
                | _ ->
                    Util.warn ("exec_VarAssign: second argument of ArrayWrite '"
                               ^ PrintAst.pf arrObj ^ "' is not a variable.");
                    let arr = (PrintAst.pf arrObj) in
                      arr, arr ^ "[" ^ (PrintAst.pf index) ^ "]"
            in
            let new_state = replace_ArrValue array ident v state in
              debug_lmsg 4 (fun () -> "state after assignment:\n"
                                      ^ show_state "    " new_state);
              new_state
        | rhs -> Util.fail ("exec_VarAssign: ill-formed array assignment '"
                            ^ PrintForm.string_of_form rhs ^ "'.\n")
    end
  else (* variable assignment *)
    let new_state = replace_VarValue assign.assign_lhs assign.assign_rhs state
    in
      debug_lmsg 3 (fun () -> "executing a value assignment:\n"
                                ^ PrintAst.pr_var_assign assign);
      debug_lmsg 4 (fun () -> "state before assignment:\n"
                              ^ show_state "    " state);
      let final_state =
        if List.mem_assoc assign.assign_lhs state.arrays
        then (* array copy *)
            let cleaned_values = (* removing the old values of the array *)
              List.filter
                (fun (name, value) -> not (is_cell assign.assign_lhs name))
                new_state.values in
              {new_state with
                 values =
                    List.fold_left
                      (fun acc (name, value) ->
                         if is_cell (unvar assign.assign_rhs) name
                         then
                           (Scanf.sscanf name "%s[%s]"
                              (fun _ -> sprintf "%s[%s]" assign.assign_lhs),
                            value)
                           :: acc
                         else acc)
                      cleaned_values
                      cleaned_values}
        else (* simple variable assignment *)
          new_state
      in
        debug_lmsg 4 (fun () ->  "state after assignment:\n"
                                 ^ show_state "    " final_state);
        final_state
      
let exec_Alloc alloc state =
  debug_lmsg 3 (fun () -> "executing an 'Alloc' command:\n"
                          ^ PrintAst.pr_alloc alloc);
  {state with
     values = mk_undef alloc.alloc_lhs
              :: List.remove_assoc alloc.alloc_lhs state.values}

let exec_ArrayAlloc alloc state =
  debug_lmsg 3 (fun () -> "executing an 'ArrayAlloc' command:\n"
                          ^ PrintAst.pr_array_alloc alloc);
  {state with
     values = (alloc.arr_alloc_lhs, mk_var ("newarray_" ^ alloc.arr_alloc_lhs))
              :: List.remove_assoc alloc.arr_alloc_lhs state.values;       
     arrays =
      (alloc.arr_alloc_lhs, List.map (subst state.values) alloc.arr_alloc_dims)
      :: state.arrays}

let exec_Assert (assertion : hint_annot_form_command) (state : state) =
  debug_lmsg 3 (fun () -> "executing an 'assert' command\n");
  state

let exec_NoteThat (note : hint_annot_form_command) (state : state) =
  debug_lmsg 3 (fun () -> "executing a 'noteThat' command\n");
  state

let exec_Assume (assume : annot_form_command) (state : state) =
  debug_lmsg 3 (fun () -> "executing a 'assume' command:\nadding formula \""
                          ^ PrintAst.pf assume.annot_form
                          ^ "\" to verification conditions\n");
  {state with
     verification_condition = (subst state.values assume.annot_form)
                              :: state.verification_condition}
let exec_Split (split : annot_form_command) (state : state) =
  debug_lmsg 3 (fun () -> "executing a 'split' command\n");
  state
  
(* 'havoc x' == 'x := any_x' *)
let exec_Havoc havoc state =
  debug_lmsg 3 (fun () -> "executing a 'havoc' command:\n"
                          ^ PrintAst.pr_havoc havoc);
  debug_lmsg 4 (fun () -> "state before 'havoc':\n" ^ show_state "    " state);
  let vars = AstUtil.get_havoc_vars havoc in
  let assignments = List.map
                      (fun x -> {assign_lhs = x;
                                 assign_tlhs = (x,TypeUniverse);
                                 assign_rhs = any x})
                      vars in
  let new_state =
    {(List.fold_left (fun s c -> exec_VarAssign c s) state assignments) with
       path_condition =
        match havoc.havoc_constraint with
          | None -> state.path_condition
          | Some const -> (subst state.values const) :: state.path_condition}
  in
    debug_lmsg 4 (fun () -> "state after 'havoc':\n"
                            ^ show_state "    " new_state);
    new_state

let rec exec_ProcCall procCall state =
  debug_lmsg 3 (fun () -> "executing a 'procCall' command to \""
                  ^ procCall.callee_module ^ "." ^ procCall.callee_name
                  ^ "\".\n");
  let formal_res = (* formal result *)
    exec_proc procCall.callee_module procCall.callee_name in

  (** substitution of arguments and result value *)
  (* list of (formal argument name, real argument) *)
  let argument_map =
    List.combine 
      (List.map AstUtil.name_of_vd (Util.unsome procCall.callee_hdr).p_formals)
      procCall.callee_args in
  let global_map =
    (List.map
       (fun (name, value) -> unvar (init name), List.assoc name state.values)
       (fst (make_mod_vars procCall.callee_module))) in
    (* list of states with values containing (formal result name, real result) *)
  let formal_result =
    List.map (apply_subst (argument_map @ global_map)) formal_res in
    (* mapping the result *)
  let result_map =
    [result_var,
     mk_var (Util.safe_unsome "intermediate_result" procCall.callee_res)] in
    (* list of out-context states with good values *)
  let real_result = List.map (apply_subst result_map) formal_result in
  let result = List.map (fun state1 -> merge_state state1 state) real_result
  in
    debug_lmsg 4 (fun () -> "state before call:\n" ^ show_state "    " state);
    debug_lmsg 5 (fun () -> "formal_res =\n"
                    ^ String.concat "\n"
                    (List.map (show_state "    ") formal_res));
    debug_lmsg 5 (fun () -> "argument_map = " ^ pr_substMap argument_map ^"\n");
    debug_lmsg 5 (fun () -> "global_map = " ^ pr_substMap global_map ^"\n");
    debug_lmsg 5 (fun () -> "formal_result =\n"
                    ^ String.concat "\n"
                    (List.map (show_state "    ") formal_result));
    debug_lmsg 5 (fun () -> "result_map = " ^ pr_substMap result_map ^"\n");
    debug_lmsg 5 (fun () -> "real_result =\n"
                    ^ String.concat "\n"
                    (List.map (show_state "    ") real_result));
    debug_lmsg 4 (fun () -> "states after call:\n"
                    ^ String.concat "\n"
                    (List.map (show_state "    ") result));
    result
      
and exec_bc basic_command state =
  match basic_command with
    | Skip -> [run exec_Skip state]
    | Hint h -> [run (exec_Hint h) state]
    | VarAssign ac -> [run (exec_VarAssign ac) state]
    | Alloc ac -> [run (exec_Alloc ac) state]
    | ArrayAlloc aac -> [run (exec_ArrayAlloc aac) state]
    | Assert h -> [run (exec_Assert h) state]
    | NoteThat nt -> [run (exec_NoteThat nt) state]
    | Assume a -> [run (exec_Assume a) state]
    | Split s -> [run (exec_Split s) state]
    | Havoc hc -> [run (exec_Havoc hc) state]
    | ProcCall pc -> if state.returned then [state] else exec_ProcCall pc state
    | Instantiate _ -> Util.fail "exec_bc: instantiate should be desugared.\n"
    | Mp _ -> Util.fail "exec_bc: mp should be desugared.\n"

(** {3 for full command} *) 

and exec_Seq cmd_list state_list =
  debug_lmsg 3 (fun () -> "executing a sequence of commands\n");
  List.fold_left (fun st c -> exec_command c st) state_list cmd_list
    
and exec_Choice cmd_list state_list =
  debug_lmsg 3 (fun () -> "executing a 'choice' command\n");
  List.concat (List.map (fun c -> exec_command c state_list) cmd_list)

and exec_If {if_condition = ic; if_then = it; if_else = ie} state_list =
  debug_lmsg 3 (fun () -> "executing a 'if' command\n");
  List.append
    (exec_command it      (* true branch *)
       (List.map (* adding 'ic' to states *)
          (fun state -> run (add_path_condition (subst state.values ic)) state)
          state_list))
    (exec_command ie      (* false branch *)
       (List.map (* adding 'not ic' to states *)
          (fun state ->
             run (add_path_condition (smk_not (subst state.values ic)))
               state)
          state_list))

and exec_Loop {loop_ppoint = pp; loop_inv = inv; loop_prebody = body1;
               loop_test = test; loop_postbody = body2}
    state_list =
  debug_lmsg 3 (fun () -> "executing a 'loop' command\n");
  let subst_mod =       (* modified variables by previous *)
    List.map mk_unknown (* iteration have unknown values  *)
      (Util.union
         (AstUtil.get_modified_vars body1)
         (AstUtil.get_modified_vars body2)) in
  let arbitrary_body1 =
    exec_command body1 (List.map (apply_subst subst_mod) state_list) in
  let add_test valid state =
    if valid (* test passed *)
    then
      add_path_condition
        (subst state.values test)
        (add_path_condition (Util.safe_unsome mk_true inv) state)
    else
      add_path_condition
        (mk_not (subst state.values test))
        (add_path_condition (Util.safe_unsome mk_true inv) state)
  in
    List.append (* last iteration in loop *)
      (List.map (run (add_test false)) arbitrary_body1)
      (List.filter (* to catch exit statement inside loop *)
         (fun state -> state.returned)
         (exec_command body2
            (List.map (run (add_test true)) arbitrary_body1)))

and exec_Return {return_exp = ret} state_list =
  debug_lmsg 3 (fun () -> "executing a 'return' command\n");
  List.map
    (run
       (fun state ->
          {(replace_VarValue result_var
              (Util.unsome_apply (mk_var "none") (subst state.values) ret)
              state)
           with returned = true}))
    state_list

and exec_command command state_list =
  match command with
    | Basic {bcell_cmd = bc} -> List.concat (List.map (exec_bc bc) state_list)
    | Seq cl -> exec_Seq cl state_list
    | Choice cl -> exec_Choice cl state_list
    | If if_cmd -> exec_If if_cmd state_list
    | Loop loop_cmd -> exec_Loop loop_cmd state_list
    | Return ret_cmd -> exec_Return ret_cmd state_list
    | PickAny _ -> Util.fail "exec_command: pickAny should be desugared.\n"
    | PickWitness _ -> Util.fail "exec_command: pickWitness should be desugared.\n"
    | Assuming _ -> Util.fail "exec_command: assuming should be desugared.\n"
    | Induct _ -> Util.fail "exec_command: induct should be desugared.\n"
    | Contradict _ -> Util.fail "exec_command: contradict should be desugared.\n"
    | Proof _ -> Util.fail "exec_command: proof should be desugared.\n"

and local_decl (vars, arrays) local =
  match local.vd_type with
    | TypeApp (TypeArray, _) -> vars, Util.set_add (local.vd_name, []) arrays
    | _ ->
        Util.set_add
          (local.vd_name,
           Util.safe_unsome (snd (mk_undef local.vd_name)) local.vd_init)
          vars,
        arrays

and global_decl (vars, arrays) v = 
  if String.sub v.global_type 0 5 = "Array"
  then
    vars, Util.set_add (v.global_name, []) arrays
  else
    Util.set_add (v.global_name, init v.global_name) vars, arrays

and make_mod_vars =
  let mod_vars = Hashtbl.create 17 in
    fun mod_name ->
      try Hashtbl.find mod_vars mod_name
      with Not_found ->
        let mod_map = (* find the mapping of the module name *)
          List.find
            (fun map -> map.map_impl.im_name = mod_name)
            !prog.p_maps in
(* no unsome, otherwise variables start all procedures with default values *)
        let get_vars (var_acc, arr_acc) var =
          (var.vd_name, (init var.vd_name)) :: var_acc, arr_acc in
        let impl_vars = (* add module concrete variables *)
          List.fold_left get_vars !prog_vars mod_map.map_impl.im_vars in
        let this_mod_vars =  (* add module abstract variables *)
          List.fold_left
            get_vars
            impl_vars
            (Util.difference (* avoiding repetition of variables *)
               mod_map.map_spec.sm_spec_vars
               mod_map.map_impl.im_vars)
        in
          Hashtbl.add mod_vars mod_name this_mod_vars;
          this_mod_vars

and exec_proc mod_name proc_name =
  let full_name = Util.qualify_if_needed mod_name proc_name in
    try (* Result memoized *)
      let result = Hashtbl.find exec_result full_name in
        debug_lmsg 1 (fun () -> full_name ^ " already analysed.\n");
        result
    with Not_found ->
      debug_lmsg 1 (fun () -> full_name
                      ^ " not yet analysed, starting analysis.\n");
      let impl = AstUtil.must_find_im mod_name !prog in
      let proc_def = AstUtil.must_find_proc proc_name impl in
      let initial_vars =
        List.fold_left
          local_decl
          (make_mod_vars impl.im_name)
          proc_def.p_locals in
      let initial_state = { values = fst initial_vars;
                            arrays = snd initial_vars;
                            path_condition = [];
                            verification_condition = [];
                            returned = false } in
        debug_lmsg 2 (fun () -> "Initial state for procedure "
                        ^ proc_def.p_header.p_name ^ ":\n"
                        ^ show_state "    " initial_state);
        let symbolic_res = exec_command proc_def.p_body [initial_state] in
        let local_names = List.map AstUtil.name_of_vd proc_def.p_locals in
        let purified_res =
          purify_states (fun name -> List.mem name local_names) symbolic_res
        in
          Hashtbl.add exec_result full_name purified_res;
          debug_lmsg 1 (fun () -> "analysis of " ^ full_name ^ " done.\n");
          symbolic_res

let analyse_method mod_name meth_name =
  print_paths mod_name meth_name (exec_proc mod_name meth_name)

let analyse_class impl_name =
  let impl = AstUtil.must_find_im impl_name !prog in
    printf "\n  -----  Starting analysis of module %s  -----\n" impl.im_name;
    debug_lmsg 1 (fun () -> "Common variables to module " ^ impl.im_name ^":\n"
                            ^ show_vars (make_mod_vars impl.im_name));
    List.iter
      (analyse_method impl_name)
      (List.map (fun p -> p.p_header.p_name) impl.im_procs)

let do_it (program : program) (task : Common.analysis_task) : bool =
  if !CmdLine.sastVC
  then
    Util.fail "SymbolicExecution: symbolic execution does not work \
               with simplified AST, use -nosastvc option."
  else
    begin
      prog := program;
      (* Define Jahob and program-wide variables *)
      prog_vars := List.fold_left global_decl internal_defs !prog.p_globals;
      debug_lmsg 1
        (fun () ->
           "Initial variables of the program (plus Jahob internal variables ["
           ^ String.concat ", " internal_vars ^ "]):\n"
           ^ show_vars !prog_vars);
      if not (task.Common.task_lemmas = []) then
        Util.warn "SymbolicExecution: lemmas not proved.";
      if (task.Common.task_methods = [] && task.Common.task_classes = [])
      then
        List.iter
          analyse_class
          (List.map (fun impl -> impl.im_name) program.p_impls)
      else
        begin
          List.iter (Util.uncurry analyse_method) task.Common.task_methods;
          List.iter analyse_class task.Common.task_classes;
        end;
      printf "End of symbolic execution\n";
      true (* meaningless return value *)
    end
