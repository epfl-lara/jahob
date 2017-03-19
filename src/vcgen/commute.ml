(** Commutativity Analysis *)

(* General idea:
 * - check separability of all methods into update and invocation parts
 *   -> update == perform all filed and variable update
 *   -> invocation == only calls to some methods (possibibly reccursive calls)
 * - all methods must be in the following form: update part THEN invocation part
     (now only update OR invocation)
 * - try to test wether all calls plus update parts into a procedure commute
 * - if it fails, try to increase granularity by inlining non commuting methods
 *   (the update part must still be BEFORE the invocation one)
 *)

(* TODO: 1) Allow equivalence condition on something else than variables
            and fields (mostly on return value or a semantic condition)
         2) Make assert testing work because results can be unsound otherwise
         3) Make a data dependency analysis to be able to automatically
            determine flow controls that can be parallelized
         3) What about allowing precondition invariants that would be assumed 
            to hold before and would have ot hold after the calls?
            (especially for private methods)
         4) Save all code already extracted to avoid having to re-extract it
            at each new commutativity test. But do not forget to remove the
            storage when 'inlined' is modified and to rename the arguments!
 *)

(* BUGS: look for XXX in the code *)
open Ast
open AstUtil
open Common
open Form
open FormUtil
open Printf

(* These are shorthands for printing debug messages for this module. *)
let debug_id = Debug.register_debug_module "Commute"
let debug_msg = Debug.debug_msg debug_id
let debug_lmsg = Debug.debug_lmsg debug_id
let debug_is_on ?(level=1) () =
  Debug.debug_is_on debug_id && !Debug.debug_level >= level


(*********************************************)
(* {6 Types and constant values definitions} *)
(*********************************************)


type proc_def_env = impl_module * proc_def * ident

let ignore_asserts = "Commute"

(* we assume that no user variable has on of these names *)
let internal_vars = [all_alloc_objs; arrayName] (* what about Module.hidden? *)

(* Global reference to the program *)
let prog : program ref = ref empty_prog

(* Global reference to inlined methods *)
let inlined : string list ref = ref []


(*******************************************)
(* {6 Printing and variable name handling} *)
(*******************************************)


let print_ident_list level nm ids =
  debug_lmsg level (fun () -> nm ^ ": [ " ^ String.concat " " ids ^ " ]\n")

let print_extent level str extent =
  debug_lmsg level
    (fun () -> str ^ "[ "
       ^ String.concat " " (List.map (fun (_, _, mn) -> mn) extent) ^ " ]\n")

let show_rename_map rm =
  let pad = "    " in
    pad
    ^ String.concat ("\n" ^ pad)
        (List.map (fun (x, y) -> x ^ " -> " ^ (PrintAst.pf y)) rm)
    ^ "\n"

let orderA_suffix = "__A"
let orderB_suffix = "__B"
let orderA_id id = id ^ orderA_suffix
let orderB_id id = id ^ orderB_suffix

let commutativity_prefix = "arg_comm"
let init_suffix = Sast.init_suffix (* required for compatibility *)
let commute_id = fun () -> Util.fresh_name commutativity_prefix
let is_commute_id id =
  let match_exp =
    Str.regexp (commutativity_prefix ^ "_[0-9]+[\\(" ^ orderA_suffix
                ^ "\\)\\|\\(" ^ orderB_suffix ^ "\\)]?")
  in
    Str.string_match match_exp id 0

let is_this vd = vd.vd_name = this_id
let mk_id vd = if is_this vd then this_id else commute_id ()
let init id = id ^ init_suffix

let is_init_id id =
  let match_exp =
    Str.regexp (".+" ^ init_suffix ^ "[\\(" ^ orderA_suffix
                ^ "\\)\\|\\(" ^ orderB_suffix ^ "\\)]?")
  in
    Str.string_match match_exp id 0


(***************************)
(* {6 Renaming operations} *)
(***************************)


let rename_vars = List.map (fun name -> name, mk_var (Util.fresh_name name))

let mk_rename_map ids ident_map =
  let renamed_ids = List.map ident_map ids in
    List.combine ids (List.map mk_var renamed_ids)

let mk_rename_map_for_pd pd = mk_rename_map (get_locals pd)

let replace_if_match rm id =
  try match List.assoc id rm with
    | Var replace_id -> replace_id
    | f -> Util.fail ("replace_if_match expects Var instead of " ^
                        (PrintAst.pf f))
  with Not_found -> id

let typeForm_of_typedIdent (id, tf) = tf

let rename_ident_of_typedIdent rm (id, tf) =
  replace_if_match rm id, tf

let rename_assign_command rm ac =
  let renamed_lhs = replace_if_match rm ac.assign_lhs in
  let renamed_ac =
    { assign_lhs = renamed_lhs;
      assign_tlhs = (renamed_lhs, typeForm_of_typedIdent ac.assign_tlhs);
      assign_rhs = (subst rm ac.assign_rhs) } in
    debug_lmsg 2
      (fun () -> "BEFORE: " ^ 
         PrintAst.pr_command (mkbasic (VarAssign ac)) ^ "\n");
    debug_lmsg 2
      (fun () -> "AFTER: " ^ 
         PrintAst.pr_command (mkbasic (VarAssign renamed_ac)) ^ "\n");
    renamed_ac

let rename_alloc_command rm ac =
  let renamed_lhs = replace_if_match rm ac.alloc_lhs in
    { alloc_lhs = renamed_lhs;
      alloc_tlhs = (renamed_lhs, typeForm_of_typedIdent ac.alloc_tlhs);
      alloc_type = ac.alloc_type }

let rename_array_alloc_command rm aac =
  let renamed_lhs = replace_if_match rm aac.arr_alloc_lhs in
    { arr_alloc_lhs = renamed_lhs;
      arr_alloc_tlhs = (renamed_lhs, typeForm_of_typedIdent aac.arr_alloc_tlhs);
      arr_alloc_type = aac.arr_alloc_type;
      arr_alloc_dims = List.map (subst rm) aac.arr_alloc_dims }

let rename_hint_annot_form_command rm hafc =
    { hannot_form = subst rm hafc.hannot_form;
      hannot_about = Util.some_apply (replace_if_match rm) hafc.hannot_about;
      hannot_msg = hafc.hannot_msg;
      hannot_hints = List.map (replace_if_match rm) hafc.hannot_hints;
      hannot_forSuch = List.map (replace_if_match rm) hafc.hannot_forSuch; }

let rename_annot_form_command rm afc =
    { annot_form = subst rm afc.annot_form;
      annot_about = Util.some_apply (replace_if_match rm) afc.annot_about;
      annot_msg = afc.annot_msg; }

let rename_havoc_command rm hc =
  { havoc_regions = List.map (subst rm) hc.havoc_regions;
    havoc_msg = hc.havoc_msg;
    havoc_constraint = Util.some_apply (subst rm) hc.havoc_constraint;
    havoc_internal = hc.havoc_internal}

let rename_proc_call rm pc =
  { pc with
      callee_res = Util.some_apply (replace_if_match rm) pc.callee_res;
      callee_args = List.map (FormUtil.subst rm) pc.callee_args }
      
let rename_hint rm (TrackSpecvar { track_var = tv }) =
        TrackSpecvar { track_var = replace_if_match rm tv; }

let rename_instantiate rm ic =
  { ic with
      instantiate_form = FormUtil.subst rm ic.instantiate_form;
      instantiate_with = List.map (FormUtil.subst rm) ic.instantiate_with }

let rename_mp rm mc =
  { mc with
      mp_form = FormUtil.subst rm mc.mp_form }

let rec combine_rename_maps rm0 rm1 =
  match rm0 with
    | [] -> rm1
    | (id, f) :: rm0_q ->
        if List.mem_assoc id rm1
        then combine_rename_maps rm0_q rm1
        else (id, f) :: (combine_rename_maps rm0_q rm1)

let rename_bc rename_map = function
  | Skip -> Skip
  | VarAssign ac -> VarAssign (rename_assign_command rename_map ac)
  | Alloc ac -> Alloc (rename_alloc_command rename_map ac)
  | ArrayAlloc aac -> ArrayAlloc (rename_array_alloc_command rename_map aac)
  | Assert hafc -> Assert (rename_hint_annot_form_command rename_map hafc)
  | NoteThat hafc -> NoteThat (rename_hint_annot_form_command rename_map hafc)
  | Assume afc -> Assume (rename_annot_form_command rename_map afc)
  | Split afc -> Split (rename_annot_form_command rename_map afc)
  | Havoc hc -> Havoc (rename_havoc_command rename_map hc)
  | ProcCall pc -> ProcCall (rename_proc_call rename_map pc)
  | Hint h -> Hint (rename_hint rename_map h)
  | Instantiate ic -> Instantiate (rename_instantiate rename_map ic)
  | Mp mc -> Mp (rename_mp rename_map mc)

(**********************************************************************)
(* {6 Testing properties of the program and extraction of infomation} *)
(**********************************************************************)


(* Formulas do not contain method invocations. *)
let no_calls f = true

let ucommand = function
  | ProcCall {callee_module = mn; callee_name = pn} ->
      List.mem (Util.qualify mn pn) !inlined
  | _ -> true

let rec iform local_vars = function
  | Var id -> List.mem id local_vars
  | Const c -> 
      begin
        match c with
            (* Are array reads and writes safe? For now
               conservatively assume not. *)
          | ArrayRead | ArrayWrite | FieldRead | FieldWrite -> false
          | _ -> true
      end
  | App(f0, fl) -> (iform local_vars f0) && List.for_all (iform local_vars) fl
  | Binder(_, til, f0) -> 
      let il, _ = List.split til in
        iform (Util.union local_vars il) f0
  | TypedForm(f0, _) -> iform local_vars f0

let icommand local_vars ghosts = function
      | VarAssign { assign_lhs = id; assign_rhs = f } ->
          (List.mem id ghosts) (* writing a ghost specvar *)
          || ((List.mem id local_vars) && (iform local_vars f)) (* local vars *)
            (* field of a local object, modification cannot escape local scope,
               otherwise there is a global assignment to make it reachable *)
          || (is_field id !prog && List.mem (recv_of_field f) local_vars)
      | Alloc { alloc_lhs = id } -> List.mem id local_vars
      | ArrayAlloc { arr_alloc_lhs = id; arr_alloc_dims = fl } ->
          (List.mem id local_vars) && (List.for_all (iform local_vars) fl)
      | ProcCall { callee_module = mn; callee_name = pn;
                   callee_res = ido; callee_args = fl } ->
          let call = not (List.mem (Util.qualify mn pn) !inlined) in
          let res = match ido with
            | None -> true
            | Some id -> List.mem id local_vars in
          let args = List.for_all (iform local_vars) fl in
            call && res && args
      | _ -> true

let rec test_command ?testseq ?testch ?testif ?testloop testbc testf default c =
  debug_lmsg 5 (fun () -> "test_command: " ^ (PrintAst.pr_command c));
  let test_cmd =
    test_command ?testseq ?testch ?testif ?testloop testbc testf default in
  match c with 
    | Basic { bcell_cmd = bc } -> testbc bc
    | Seq cl -> 
        begin
          match testseq with
            | Some test -> test test_cmd testf default cl
            | None -> List.for_all test_cmd cl
        end
    | Choice cl -> 
        begin
          match testch with
            | Some test -> test test_cmd testf default cl
            | None -> List.for_all test_cmd cl
        end
    | If ({ if_condition = ic; if_then = it; if_else = ie } as if_cmd) ->
        begin
          match testif with
            | Some test -> test test_cmd testf default if_cmd
            | None -> (testf ic) && (test_cmd it) && (test_cmd ie)
        end
    | Loop ({ loop_prebody = lpre; loop_test = ltest;
              loop_postbody = lpost } as loop_cmd) ->
        begin
          match testloop with
            | Some test -> test test_cmd testf default loop_cmd
            | None -> (test_cmd lpre) && (testf ltest) && (test_cmd lpost)
        end
    | Assuming _
    | PickAny _ 
    | PickWitness _
    | Induct _ 
    | Contradict _ 
    | Proof _ -> default
    | Return { return_exp = reo } -> Util.unsome_apply default testf reo

let imethod (_, pd, name) =
  let local_vars = AstUtil.get_locals pd in
  let ghosts = get_ghostvars !prog in
  let result =
    not (List.mem (Util.unqualify2 name) !CmdLine.notParallel)
    && test_command
      (icommand local_vars ghosts) (iform local_vars) true pd.p_body in
    if result
    then
      debug_lmsg 2 (fun () -> name ^ " is an invocation method.\n")
    else
      debug_lmsg 2 (fun () -> name ^ " is not an invocation method.\n\n");
    result

let umethod (_, pd, name) =
  let result =
    (List.mem (Util.unqualify2 name) !CmdLine.notParallel)
    || test_command ucommand no_calls true pd.p_body in
    if result
    then debug_lmsg 2 (fun () -> name ^ " is an object method.\n")
    else
      debug_lmsg 2
        (fun () -> name ^ " is not an object method.\n\n");
    result

let check_decomp ((_, _, name ) as proc) =
  let result = (imethod proc) || (umethod proc) in
    if not result then
      Util.fail ( name ^ " is not an update method or an invocation method.");
    result

let rec is_trivial = function
    | Const (BoolConst true) -> true
    | TypedForm (f, _) -> is_trivial f
    | App (Const Comment, [_; f]) -> is_trivial f
    | _ -> false

let filter_trivial f = not (is_trivial f)

let no_calls_inlined = function
  | ProcCall { callee_module = cn; callee_name = mn } ->
      let fn = Jast2ast.c_name cn mn in
      let not_inlined = not (List.mem fn !inlined) in
        if not_inlined
        then debug_lmsg 2 (fun () -> fn ^ " is not an inlined procedure.\n")
        else debug_lmsg 1 (fun () -> fn ^ " is an inlined procedure.\n");
        not_inlined
  | _ -> true

let no_calls_inline pd =
  print_ident_list 1 "Inlined procedures" !inlined;
  debug_lmsg 2 (fun () -> PrintAst.pr_proc_def "" pd);
  test_command no_calls_inlined no_calls true pd.p_body

let get_proc_info (mod_name, proc_name) =
  let impl = must_find_im mod_name !prog in
  let name = Jast2ast.c_method_name mod_name proc_name in
    (impl, must_find_proc name impl, Jast2ast.c_name mod_name proc_name)

let get_proc_def proc_name =
  let _, result, _ = get_proc_info proc_name in
    result


(***********************************)
(* {6 Creating auxiliary formulae} *)
(***********************************)


let mk_null_check id =
  mk_assert (mk_neq ((Var id), mk_null)) (id ^ "_NotNullCheck")

let mk_assumes_from_vd vd id =
  match vd.vd_jtype with
    | Some ty ->   
        let idf = mk_typedform((mk_var id), (mk_object_type)) in
        let tyf = mk_typedform((mk_var ty), (mk_obj_set_type)) in
          [(mk_assume_about
              id
              (mk_and [mk_elem(idf, tyf); mk_elem(idf, Ast.all_alloc_objsf)])
              (id ^ "_type"))]
    | None -> []

let mk_proccall im p =
  debug_lmsg 1 (fun () -> "\n!!! Entering mk_proccall. !!!\n");
  debug_lmsg 2 (fun () -> p.p_header.p_name ^ " has Java return type "
                  ^ Util.safe_unsome "???" p.p_header.p_jtype ^ ".\n");
  let res_option =
    match p.p_header.p_restype with
      | TypeApp(TypeUnit, []) -> None
      | _ -> Some (commute_id ()) in
    (* (Some id, [id]) in *)
    (* The return value should be one of the criteria that
       determines whether or not a method commutes with another. *)
  let arg_vds = p.p_header.p_formals in
  let args = List.map mk_id arg_vds in (* create arbitrary arguments *)
  print_ident_list 1 "args"
    (List.map2 (fun x y -> x.vd_name ^ "->" ^ y) p.p_header.p_formals args);
  let pc = { callee_res = res_option;
             callee_module = im.im_name;
             callee_name = p.p_header.p_name;
             callee_hdr = Some p.p_header;
             callee_args = List.map mk_var args;
             call_is_external = p.p_header.p_public } in
  let call = Basic { bcell_cmd = ProcCall pc;
                     bcell_point = dummy_program_point;
                     bcell_known_before = [];
                     bcell_known_after = [] } in
  let assumes = List.flatten (List.map2 mk_assumes_from_vd arg_vds args) in
  let cmd =
    (* first argument is the receiver *)
    if ((List.length arg_vds) > 0) && not (is_this (List.hd arg_vds))
      (* the receiver must be non null *)
    then smk_cmd_seq (assumes @ [mk_null_check (List.hd args); call])
      (* 'this' is already known to be non null *)
    else smk_cmd_seq (assumes @ [call]) in
    (cmd, args)

(* Create a formula saying that for all object in [operation Object.alloc]
   in both execution order, the field has same value. The paramenter
   [operation] permits switching from current to old allocated objects. *)
let prepare_fld_eqs operation fld =
  debug_lmsg 2 (fun () -> "\n!!! Entering mk_*_fld_eqs. !!!\n");
  let xid = "framedObj" in
  let xvar = mk_var xid in
  let xtypename = Util.unqualify_getting_module fld in
  let all_alloc_objsA = mk_var (orderA_id (operation all_alloc_objs)) in
  let all_alloc_objsB = mk_var (orderB_id (operation all_alloc_objs)) in
  let elem = mk_and[mk_elem(xvar, all_alloc_objsA);
                    mk_elem(xvar, all_alloc_objsB);
                    mk_elem(xvar, mk_var (obj_var xtypename))] in
  let notrep = (* not sure what this line does. copied from sast. *)
    if !CmdLine.tokens
    then [mk_neq(mk_old_owner_of xvar, mk_class_token xtypename)]
    else []
  in
  let lhs = smk_and (elem::notrep) in
  let rhs = mk_eq(mk_fieldRead (mk_var (orderA_id fld)) xvar,
                  mk_fieldRead (mk_var (orderB_id fld)) xvar) in
  mk_forall (xid, mk_object_type, smk_impl(lhs,rhs))

let mk_fld_eqs = prepare_fld_eqs (fun x -> x)

let mk_init_fld_eqs = prepare_fld_eqs init

let mk_lv_eqs x = smk_eq (Var (orderA_id x)) (Var (orderB_id x))

let mk_init_var_eqs to_init = mk_lv_eqs (init to_init)


(******************************)
(* {6 Commutativity analysis} *)
(******************************)


let prove names formulae =
  (* to avoid mixing stats with the sanity check! *) 
 if debug_is_on () then Decider.clear_stats ();
  debug_lmsg 1 (fun () -> "\n!!! Entering prove. !!!\n");
  debug_lmsg 2 (fun () -> "There is " ^ string_of_int (List.length formulae)
                  ^ " " ^ names ^ " to prove.\n");
  let name = String.sub names 0 (String.length names - 1) in
  let result =
    List.fold_left
      (fun count form ->
         let res = Decider.valid form in
           if res
           then
             begin
               debug_lmsg 2 (fun () -> names ^ " proved\n");
               count
             end
           else
             begin
               debug_lmsg 2 (fun () -> "VERIFICATION FAILED on " ^ name ^ ":\n"
                                       ^ PrintAst.pf form ^ "\n\n");
               count + 1
             end)
      0
      formulae
  in
    if debug_is_on () then Decider.print_stats false;
    result


let get_callees ?name pd =
  let rec get_callees_rec callees = function
    | Basic { bcell_cmd = ProcCall pc } ->
        Util.set_add (pc.callee_module, pc.callee_name) callees
    | Seq cl
    | Choice cl -> 
        List.fold_left get_callees_rec callees cl
    | If { if_then = c0; if_else = c1 }
    | Loop { loop_prebody = c0; loop_postbody = c1 } ->
        get_callees_rec (get_callees_rec callees c0) c1
    | Basic _
    | Assuming _
    | PickAny _
    | PickWitness _
    | Return _ 
    | Induct _ 
    | Contradict _ 
    | Proof _ -> callees
  in
  let real_name = Util.safe_unsome (name_of_pd pd) name in
  let result = get_callees_rec [] pd.p_body in
    if result = [] then
      printf "%s does not invoke any methods.\n\n" real_name
    else
      begin
        printf "%s directly invokes:\n" real_name;
        List.iter
          (Util.uncurry (printf "    %s.%s\n"))
          result;
        printf "\n"
      end;
    result

let compute_callee_multiset (im, pd, id) =
  let rec get_callees_rec callees = function
    | Basic { bcell_cmd = ProcCall pc } ->
        (* Since we want to have all fields but the last one equal,
           we just set it to an arbitrary common value *)
        if List.mem (Util.qualify pc.callee_module pc.callee_name) !inlined
        then callees
        else {pc with call_is_external = false } :: callees
    | Seq cl
    | Choice cl -> 
        List.fold_left get_callees_rec callees cl
    | If { if_then = c0; if_else = c1 }
    | Loop { loop_prebody = c0; loop_postbody = c1 } ->
        get_callees_rec (get_callees_rec callees c0) c1
    | Basic _
    | Assuming _
    | PickAny _
    | PickWitness _
    | Return _ 
    | Induct _ 
    | Contradict _ 
    | Proof _ -> callees
  in
    if
      List.mem id !inlined || List.mem (Util.unqualify2 id) !CmdLine.notParallel
    then []
    else get_callees_rec [] pd.p_body

let compute_extent (im, pd, name) =
  let rec compute_extent_rec called = function
    | [] -> called
    | ((im, pd, name) as proc) :: to_analyse ->
        let new_called = called @ [proc] in
          if List.mem (Util.unqualify2 name) !CmdLine.notParallel
          then
            begin (* sequential method: all calls are considered inlined *)
              printf "%s is considered atomic by use of the \
                      '-notparallel' option.\n\n" name;
              compute_extent_rec new_called to_analyse
            end
          else
            let callees = List.map get_proc_info (get_callees ~name pd) in
            let new_to_analyse =
              Util.union to_analyse (Util.difference callees new_called) in
              compute_extent_rec new_called new_to_analyse
  in
    (* The root method should not be in the extent (unless it's
       invoked recursively), so we start by putting its callees into a
       worklist.  *)
  let wl = List.map get_proc_info (get_callees ~name pd) in
  let result = compute_extent_rec [] wl in
    print_extent 0 ("The extent of " ^ name ^ " is: ") result;
    result

let extract_invocation_section pd rename_map =
  let rec extract = function
    | Basic ({bcell_cmd = ProcCall {callee_name = cn}} as bc)
        when not (List.mem cn !inlined) ->
        (* XXX: WRONG if the call is followed by another inlined one *)
        Basic { bc with bcell_cmd = Skip }
    | Basic bc -> Basic {bc with bcell_cmd = rename_bc rename_map bc.bcell_cmd}
    | Seq cl -> Seq (List.map extract cl)
    | Choice cl -> Choice (List.map extract cl)
    | If ic ->
        If { ic with if_condition = subst rename_map ic.if_condition }
    | Loop lc ->
        Loop { loop_ppoint = lc.loop_ppoint;
               loop_inv = Util.some_apply (subst rename_map) lc.loop_inv;
               loop_prebody = extract lc.loop_prebody;
               loop_test = subst rename_map lc.loop_test;
               loop_postbody = extract lc.loop_postbody }
    | Return rc -> 
        Return { return_exp = Util.some_apply (subst rename_map) rc.return_exp }
    | PickAny pc ->
        PickAny { pa_vars =
                    List.map (rename_ident_of_typedIdent rename_map) pc.pa_vars;
                  pa_hyp = Util.some_apply (subst rename_map) pc.pa_hyp;
                  pa_hypAnnot = pc.pa_hypAnnot;
                  pa_body = List.map extract pc.pa_body }
    | PickWitness pw ->
        PickWitness 
	  { pw_vars =
              List.map (rename_ident_of_typedIdent rename_map) pw.pw_vars;
            pw_hyp = Util.some_apply (subst rename_map) pw.pw_hyp;
            pw_hypAnnot = pw.pw_hypAnnot;
            pw_body = List.map extract pw.pw_body }
    | Assuming ac ->
        Assuming { assuming_hyp = subst rename_map ac.assuming_hyp;
                   assuming_hypAnnot = ac.assuming_hypAnnot;
                   assuming_body = List.map extract ac.assuming_body;
                   assuming_goal = 
                     rename_hint_annot_form_command rename_map ac.assuming_goal}
    | Induct ic ->
	Induct { induct_var = rename_ident_of_typedIdent rename_map ic.induct_var;
		 induct_form = subst rename_map ic.induct_form;
		 induct_annot = ic.induct_annot;
		 induct_body = List.map extract ic.induct_body}
    | Contradict cc ->
	Contradict { contradict_form = subst rename_map cc.contradict_form;
		     contradict_annot = cc.contradict_annot;
		     contradict_body = List.map extract cc.contradict_body}
    | Proof pc ->
	Proof { proof_body = List.map extract pc.proof_body;
		proof_goal = 
	    rename_hint_annot_form_command rename_map pc.proof_goal}
  in
    extract pd.p_body

let extract_code im pd ident_map =
  debug_lmsg 1 (fun () -> "\n!!! Entering extract_code. !!!\n");
  if umethod (im, pd, Util.qualify im.im_name (name_of_pd pd))
  then mk_proccall im pd
  else
    let rm = mk_rename_map_for_pd pd ident_map in
    let ids = List.map (fun (name, var) -> unvar var) rm in
    let cmd = extract_invocation_section pd rm in
      (* ids = arguments + tmp_* *)
      (cmd, List.filter (fun x -> not (Javajast.is_tmp x)) ids)


let equivalent_final calls_args postcondition_A postcondition_B =
  debug_lmsg 1 (fun () -> "\n!!! Entering equivalent_final. !!!\n");
  print_ident_list 1 "calls_args (= calls arguments)" calls_args;
  debug_lmsg 4 (fun () -> "postcondition of execution A: "
                          ^ PrintAst.pf postcondition_A ^ "\n\n");
  debug_lmsg 4 (fun () -> "postcondition of execution B: "
                          ^ PrintAst.pf postcondition_B ^ "\n\n");

  (* Separation of the different kinds of variables *)
  let classnames = AstUtil.get_class_names !prog in
  let vars_A = Util.difference (FormUtil.fv postcondition_A) classnames in
  let vars_B = Util.difference (FormUtil.fv postcondition_B) classnames in
  let finals = !CmdLine.equivConds in (* names involved in equivalence conds *)
  let global_vars = internal_vars @ (Util.union finals calls_args) in
  let local_vars_A = Util.difference vars_A global_vars in
  let local_vars_B = Util.difference vars_B global_vars in
  let local_vars = (* they are made unique *)
    (List.map orderA_id local_vars_A) @ (List.map orderB_id local_vars_B) in

  (* To avoid name clashes, rename all variables *)
  let renamed_A =
    subst (mk_rename_map vars_A orderA_id) postcondition_A in
  let renamed_B =
    subst (mk_rename_map vars_B orderB_id) postcondition_B in

  (* Initialisation formulae: same initial variables/fields and arguments *)
  let flds, vars = List.partition (fun x -> AstUtil.is_field x !prog) finals in
  let init_var_eqs = List.map mk_init_var_eqs vars in
  let init_fld_eqs = List.map mk_init_fld_eqs (List.map init flds) in
  let same_args = List.map mk_lv_eqs calls_args in
  let lhs = smk_and (init_var_eqs @ init_fld_eqs @ same_args
                     @ [renamed_A; renamed_B]) in

  (* Conclusion formulae: verifying variables and fields *)
  let var_eqs = List.map mk_lv_eqs vars in
  let fld_eqs = List.map mk_fld_eqs flds in
  let final_formulae =
    List.map (fun f -> smk_impl (lhs, f)) (var_eqs @ fld_eqs) in

    (* Debugging printings *)
    print_ident_list 1 "total vars" (Util.union vars_A vars_B);
    print_ident_list 1 "local vars" local_vars;
    print_ident_list 1 "global vars" global_vars;
    print_ident_list 1 "finals" finals;
    print_ident_list 1 "final flds" flds;
    print_ident_list 1 "final vars" vars;
    debug_lmsg 4 (fun () ->
                    "final_formula_A: " ^ (PrintAst.pf renamed_A) ^ "\n\n");
    debug_lmsg 4 (fun () ->
                    "final_formula_B: " ^ (PrintAst.pf renamed_B) ^ "\n\n");
    debug_lmsg 5 (fun () -> "formulae lhs: " ^ (PrintAst.pf lhs) ^ "\n\n");

    (* SANITY CHECK: can we prove False? *)
    if debug_is_on ()
    then
      begin
        debug_lmsg 1 (fun () -> "Starting sanity check...\n");
        let binding = List.map (fun name -> (name, TypeUniverse)) (fv lhs) in
        let sanity_check = mk_comment "sanity check"
          (smk_impl (smk_exists (binding, lhs), mk_false)) in
          debug_lmsg 5 (fun () -> PrintAst.pf sanity_check);
          if Decider.valid sanity_check
          then
            begin
              debug_lmsg 1 (fun () -> "Failed sanity check with formula:\n\n"
                              ^ PrintAst.pf sanity_check ^ "\n");
              Util.fail "equivalent_final: proved false"
            end
          else debug_lmsg 1 (fun () -> "Sanity Check succeeded!\n")
      end;

    (* Test itself *)
    debug_lmsg 5 (fun () -> "final formulae:\n"
                    ^ (String.concat "\n\n"
                         (List.map PrintAst.pf final_formulae))
                    ^ "\n");
    (prove "formulae" final_formulae) = 0


let object_sections_commute im0 im1 p0 p1 =
  debug_lmsg 1 (fun () -> "\n!!! Entering object_sections_commute. !!!\n");
  let c0, idseq_A = extract_code im0 p0 Util.fresh_name in
  let c1, idseq_B = extract_code im1 p1 Util.fresh_name in

  (* Making sequences for both orders of computation *)
  let init_this_non_null =
    mk_assume (mk_neq (this_var, mk_null)) "thisNotNull" in
  let seq_A = smk_cmd_seq [init_this_non_null; c0; c1] in
  let seq_B = smk_cmd_seq [init_this_non_null; c1; c0] in
    Sast.desugar_only_init_set ();
    let des_seq_A =
      Sast.desugar_only !prog im0 ~return_name:result_var [] seq_A in
      debug_lmsg 2 (fun () -> "sequence A " ^ PrintAst.pr_command seq_A);
      debug_lmsg 3 (fun () -> "desugared sequence A "
                      ^ PrintAst.pr_command des_seq_A);
    Sast.desugar_only_init_set ();
    let des_seq_B =
      Sast.desugar_only !prog im1 ~return_name:result_var [] seq_B in
      debug_lmsg 2 (fun () -> "sequence B " ^ PrintAst.pr_command seq_B);
      debug_lmsg 3 (fun () -> "desugared sequence B "
                      ^ PrintAst.pr_command des_seq_B);

  (* Executing strongest postcondition + dealing with asserts. *)
  debug_lmsg 2 (fun () -> "Computing strongest postconditions...");
  let post_A, all_asserts_A =
    Strongest_postcondition.sp_noloops (mk_true, []) des_seq_A in
  let post_B, all_asserts_B =
    Strongest_postcondition.sp_noloops (mk_true, []) des_seq_B in
  let asserts_A = List.filter filter_trivial all_asserts_A in
  let asserts_B = List.filter filter_trivial all_asserts_B in
    debug_lmsg 2 (fun () -> "  done\n");
    debug_lmsg 1 (fun () -> sprintf
                    "There are %i and %i (possibly trivial) assertions.\n"
                    (List.length all_asserts_A) (List.length all_asserts_B));
    debug_lmsg 1 (fun () -> sprintf
                    "There are %i and %i real assertions.\n\n"
                    (List.length asserts_A) (List.length asserts_B));
    debug_lmsg 6 (fun () -> "\nAssertions from sequence A: "
                    ^ (String.concat "\n\n"
                         (List.map PrintAst.pf asserts_A))
                    ^ "\n\n");
    debug_lmsg 6 (fun () -> "\nAssertions from sequence B: "
                    ^ (String.concat "\n\n"
                         (List.map PrintAst.pf asserts_B))
                    ^ "\n\n");
    if (List.mem ignore_asserts !CmdLine.ignore_asserts)
    then print_string "Assertions ignored: no verification.\n"
    else
      begin
        let failed_A = prove "assertions" asserts_A in
        let failed_B = prove "assertions" asserts_B in
          if failed_A <> 0 || failed_B <> 0
          then Util.warn
            (sprintf "Commute: %i and %i assertions failed" failed_A failed_B)
      end;
    equivalent_final (idseq_A @ idseq_B) post_A post_B

let check_multiset proc0 proc1 =
  let callees_0 = compute_callee_multiset proc0 in
  let callees_1 = compute_callee_multiset proc1 in
    Util.difference callees_0 callees_1 = []
    && Util.difference callees_1 callees_0 = []

let methods_commute ((im0, pd0, id0) as proc0) ((im1, pd1, id1) as proc1) =
  if ((imethod proc1) && (no_calls_inline pd1))
  then
    begin
      printf "%s is an invocation method that does not have calls \
              to inlined methods, so it commutes with %s\n\n" id1 id0;
      true
    end
  else
    begin
      printf "Checking if %s and %s commute...\n" id0 id1;
      let result_obj = object_sections_commute im0 im1 pd0 pd1 in
      let result_call = check_multiset proc0 proc1 in
        begin
          match result_obj, result_call with
            | true, true ->
                printf "%s and %s commute.\n\n" id0 id1
            | true, false -> 
                printf "The invocation sections of %s and %s \
                        do not commute.\n\n" id0 id1
            | false, true -> 
                printf "The update sections of %s and %s do not commute.\n\n"
                  id0 id1
            | false, false -> 
                printf "Neither the invocation nor the update sections of \
                        %s and %s commute.\n\n" id0 id1
        end;
        result_obj && result_call
    end

let extent_commute extent =
  let inlined = ref !CmdLine.inlined in
  let rec extent_commute_rec
      (extent : proc_def_env list)
      (processed : proc_def_env list) :
      bool * (proc_def_env list) =
    print_extent 1 "\nextent_commute on: " extent;
    match extent with
      | [] -> (true, processed)
      | ((_, pd0, mn0) as proc0) :: extent0 ->
          let imethod_result = imethod proc0 in
            if imethod_result then
              debug_lmsg 1 (fun () -> mn0 ^ " is an invocation method.\n");
            let inline_result = no_calls_inline pd0 in
              if imethod_result && inline_result then
                begin
                  printf
                    "%s is an invocation method and has no inlined calls, \
                     so it commutes with any method.\n" mn0;
                  (* recursive call on remaining methods in extent. *)
                  (extent_commute_rec extent0 (processed @ [proc0]))
                end
              else if
                (List.for_all (methods_commute proc0) extent)
              then
                begin
                  printf "%s commutes with all other methods.\n\n" mn0;
                  (* recursive call on remaining methods in extent. *)
                  (extent_commute_rec extent0 (processed @ [proc0]))
                end
              else 
                begin
                  if (processed = [] && extent0 = []) || !CmdLine.noInlining
                  then
                    begin (* all methods inlined, failure of parallelisation *)
                      printf "Verification failed for %s.\n\n" mn0;
                      (false, [])
                    end
                  else
                    begin  (* do over, but without the new inlined method *)
                      inlined := mn0 :: !inlined;
                      printf "Verification failed for %s, trying inlining it \
                              and do all over.\n\n" mn0;
                      extent_commute_rec (processed @ extent0) []
                    end
                end
  in
  let result, processed = extent_commute_rec extent [] in
    (result, !inlined, processed)

let check_commute method_names =
  let name_of_proc_def_env (_, _, x) = x
  in
  let rec check_methods ((im, pd, name) as meth) =
    debug_lmsg 1 (fun () -> "Analysing method" ^ name ^ ":\n"
                            ^ PrintAst.pr_proc_def im.im_name pd ^ "\n");
    let extent = compute_extent meth in
      (* Check that all callees are either invocation or update methods *)
      if not (List.for_all (check_decomp) extent)
      then Util.fail "check_commute: some methods cannot be decomposed in \
                      invocation or update methods.\n"
      else printf "All methods can be separated.\n\n\n";
      (* Commutativity analysis *)
      let result, inlined, not_inlined = extent_commute extent in
        printf "The methods that commute are: %s\n"
          (String.concat " " (List.map name_of_proc_def_env not_inlined));
        printf "The inlined methods are: %s\n" (String.concat " " inlined);
        printf "=== %s %s be parallelized. ===\n\n"
          (name_of_proc_def_env meth)
          (if result then "might" else "cannot");
        result
  in
    print_ident_list 1 "Methods to analyze"
      (List.map (Util.uncurry Util.qualify) method_names);
    List.fold_left (* not 'List.for_all' to try all methods *)
      (fun b meth -> check_methods meth && b)
      true
      (List.map get_proc_info method_names)

let run_class class_name =
  let impl = must_find_im class_name !prog in
    printf "\n  -----  Starting analysis of module %s  -----\n" impl.im_name;
    check_commute
      (List.map (fun pd -> impl.im_name, AstUtil.name_of_pd pd) impl.im_procs)

let run_commute program task =
  if !CmdLine.sastVC then
    Util.fail "Commutativity analysis cannot determine separability \
               with -sastvc, use '-nosastvc' option.\n"
  else
    begin
      prog := program;
      inlined := !CmdLine.inlined;
      let result = ref true in
        if not (task.task_lemmas = []) then
          Util.warn "run_commute: lemmas not proved.";
        if not (task.task_classes = []) then
          result := List.fold_left
                      (fun b name -> run_class name && b)
                      true
                      task.task_classes;
        !result && check_commute task.task_methods
    end
