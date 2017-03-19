open Ast
open Common
open Form
open FormUtil

let choose
    (relevant_defs : specvar_def list)
    (ids : ident list)
    (f : form) : form =
  fst (Vcgen.choose_with_deps relevant_defs ids f)

let choose_assign 
    (relevant_defs : specvar_def list)
    (lhs : ident) 
    (rhs : form) 
    (f : form) : form =
  (* First, conjoin definitions of dependent variables. Then do substitution. *)
  let f0, m = Vcgen.choose_with_deps relevant_defs [lhs] f in
  let lhs0 = (* find what lhs was renamed to *)
    (try List.assoc lhs m
     with Not_found -> 
       (Util.warn ("choose_assign could not find " ^ lhs); (Var lhs))) in
    smk_impl_def_eq (fun x -> true) (mk_eq (lhs0, rhs), f0)

let wp_alloc
    (prog : program)
    (relevant_defs : (ident * form) list)
    (id : ident)
    (ty : ident)
    (f : form) : form =
  (* Desugars into:
     
     havoc id;
     assume id ~: all_alloc;
     all_alloc := all_alloc Un {id};
     assume id ~= null;
     assume id : { x . x has type ty };
     assume id.f = null (for all fields f) and x.f ~= id for (for all x and f);
   *)
  let non_null = mk_neq ((Var id), mk_null) in
  let has_type = mk_elem ((Var id), Var (Ast.obj_var ty)) in
  let lonely = Background.get_unalloc_lonely_xid prog id in
  let f0 = smk_impl ((smk_and [non_null; has_type; lonely]), f) in
  let rhs = mk_cup (all_alloc_objsf, (mk_singleton (Var id))) in 
  let f1 = choose_assign relevant_defs all_alloc_objs rhs f0 in
  let not_in_alloc = mk_notelem ((Var id), all_alloc_objsf) in
    choose relevant_defs [id] (smk_impl (not_in_alloc, f1))

let wp_array_alloc 
    (prog : program)
    (relevant_defs : (ident * form) list) 
    (id : ident) 
    (dims : form list) 
    (f : form) : form =
  (* 
     id = new T[d];
     
     desugars into:
     
     havoc id;
     assume id ~: all_alloc;
     all_alloc := all_alloc Un {id};
     assume id ~= null;
     assume id.length = d;
     assume id.f = null (for all fields f) and x.f ~= id for (for all x and f);
   *)
  match dims with
    | [d] ->
	let non_null = mk_neq((Var id), mk_null) in
	let arr_length = mk_eq ((mk_arrayLength (Var id)), d) in
	let lonely = Background.get_unalloc_lonely_xid prog id in
	let f0 = smk_impl ((smk_and [non_null; arr_length; lonely]), f) in
	let rhs = mk_cup(all_alloc_objsf, (mk_singleton (Var id))) in
	let f1 = choose_assign relevant_defs all_alloc_objs rhs f0 in
	let not_in_alloc = mk_notelem ((Var id), all_alloc_objsf) in
	  choose relevant_defs [id] (smk_impl (not_in_alloc, f1))
    | _ -> failwith "\nwp_array_alloc: problem with array dimensions.\n"

let havoc 
    (relevant_defs : (ident * form) list) 
    (to_havoc : form list) 
    (f : form) : form =
  let f_to_id (f : form) : ident =
    match f with
      | Var v -> v
      | _ -> failwith ("\nweakest_precondition: havoc does not handle:\n" ^ 
			 (PrintForm.string_of_form f) ^ "\n") in
    choose relevant_defs (List.map f_to_id to_havoc) f

let mk_obligation
    (prog : program)
    (impl : impl_module)
    (relevant_defs : (ident * form) list)
    (all_deps : ident list)
    (pos : source_pos) 
    ((f, s) : (form * string)) : obligation =
  let f0 = Vcgen.assume_dependencies relevant_defs all_deps f in
  let f1 = Background.add_background_form prog impl f0 in
    { ob_pos = pos; ob_purpose = s; ob_form = f1 }


let weakest_precondition 
    (prog : program)
    (impl : impl_module)
    (proc : proc_def)
    (concretized_post : form)
    (infer : command option)
    (use_context : bool)
    (relevant_defs : (ident * form) list)
    (c : command) 
    (f : form) : (form * (form * string) list) =

  let rec wp_rec 
      (c : command) 
      ((f, vcs) : form * (form * string) list) : (form * (form * string) list) =
    match c with
      | Basic {bcell_cmd = bc} -> 
	  let f0, vcs0 = wp_bc f bc in
	    (f0, vcs0 @ vcs)
      | Seq cl -> List.fold_right wp_rec cl (f, vcs)
      | Choice cl -> 
	  let wp (c : command) = wp_rec c (f, []) in
	  let fs, list_of_vcs = List.split (List.map wp cl) in
	    (smk_and fs, (List.flatten list_of_vcs) @ vcs)
      | If {if_condition = ic; if_then = it; if_else = ie} ->
	  let it_f, it_vcs = wp_rec it (f, []) in
	  let ie_f, ie_vcs = wp_rec ie (f, []) in
	  let f0 = smk_and [smk_impl (ic, it_f); smk_impl (smk_not ic, ie_f)] in
	    (f0, it_vcs @ ie_vcs @ vcs)
      | Loop {loop_inv = invo; loop_prebody = pre;
              loop_test = test; loop_postbody = post} ->
	  let f0, vcs0 = 
	    (match invo with
	       | None -> failwith "weakest_precondition: loop invariant missing.\n"
	       | Some inv ->
		   (match infer with
		      | Some l when (l = c) -> wp_loop_infer inv pre test post f
		      | _ ->
			  if (use_context) then
			    (wp_loop_context inv pre test post f)
			  else
			    (wp_loop inv pre test post f))) in
	    (f0, vcs0 @ vcs)
      | Return {return_exp = fo} ->
	  let res =
	    (match fo with
	       | None -> concretized_post
	       | Some f0 -> subst [(result_var, f0)] concretized_post) in
	    (mk_comment "ReturnStatement" res, vcs)
      | Assuming _ -> Util.fail "wp_rec: uncaught pattern matching case \
                                 'Assuming'"
      | PickAny _ -> Util.fail "wp_rec: uncaught pattern matching case \
                                'PickAny'"
      | PickWitness _ -> Util.fail "wp_rec: uncaught pattern matching case \
                                'PickWitness'"
      | Induct _ -> Util.fail "wp_rec: uncaught pattern matching case \
                               'Induct'"
      | Contradict _ -> Util.fail "wp_rec: uncaught pattern matching case \
                                   'Contradict'"
      | Proof _ -> Util.fail "wp_rec: uncaught pattern matching case \
                              'Proof'"

  and wp_bc (f : form) (bc : basic_command) : (form * (form * string) list) =
    match bc with
      | Skip 
      | Hint _ -> (f, [])
      | VarAssign {assign_lhs = lhs; assign_rhs = rhs} ->
	  ((choose_assign relevant_defs lhs rhs f), [])
      | Alloc {alloc_lhs = lhs; alloc_type = ty} -> 
	  ((wp_alloc prog relevant_defs lhs ty f), [])
      | ArrayAlloc {arr_alloc_lhs = lhs; arr_alloc_type = ty;
                    arr_alloc_dims = dims} -> 
	  ((wp_array_alloc prog relevant_defs lhs dims f), [])
      | Assert {hannot_form = f0; hannot_msg = m} ->
	  (smk_and [mk_comment m f0; f], [])
      | NoteThat {hannot_form = f0; hannot_msg = m} ->
	  (* NoteThat desugars into an Assert followed by an Assume *)
	  let f1 = mk_comment m f0 in
	    (smk_and [f1; smk_impl (f1, f)], [])
      | Assume {annot_form = f0; annot_msg = m} ->
	  (smk_impl ((mk_comment m f0), f), [])
      | Split {annot_form = f0; annot_msg = m} ->
	  let f1 = mk_comment m f0 in
	  let vc = ((smk_impl (f0, f)), ("SPLIT_" ^ m)) in
	    (f1, [vc])
      | Havoc {havoc_regions = fs} -> 
	  ((havoc relevant_defs fs f), [])
      | ProcCall pc -> 
	  (* Desugar procedure call first and then do wp. *)
	  let c = Seq (fst (Sast.desugar_procedure_call prog impl pc)) in
	    wp_rec c (f, [])
      | Instantiate _ -> 
	  Util.fail "wp_bc: uncaught pattern matching case 'Instantiate'"
      | Mp _ -> 
	  Util.fail "wp_bc: uncaught pattern matching case 'Mp'"

  and wp_loop_infer
      (inv : form)
      (pre : command)
      (test : form)
      (post : command)
      (f : form) : (form * (form * string) list) =
    let exit_f = smk_impl ((smk_not test), f) in
    let f0, vcs0 = wp_rec pre (exit_f, []) in
    let exit_vc = ((smk_impl (inv, f0)), "LoopInvImpliesPost") in
    let f1, vcs1 = wp_rec post (inv, []) in
    let loop_f = smk_impl (test, f1) in
    let f2, vcs2 = wp_rec pre (loop_f, []) in
    let loop_vc = ((smk_impl (inv, f2)), "LoopInvPreservation") in
      (inv, loop_vc :: (vcs1 @ (exit_vc :: vcs0)))    

  and wp_loop 
      (inv : form) 
      (pre: command) 
      (test : form) 
      (post : command) 
      (f : form) : (form * (form * string) list) =
    (* This is the standard definition of the loop invariant. *)
    let exit_f = smk_impl ((smk_not test), f) in
    let f0, vcs0 = wp_rec pre (exit_f, []) in
    let exit_vc = ((smk_impl (inv, f0)), "LoopInvImpliesPost") in
    let f1, vcs1 = wp_rec post (inv, []) in
    let loop_f = smk_impl (test, f1) in
    let f2, vcs2 = wp_rec pre (loop_f, []) in
    let loop_vc = ((smk_impl (inv, f2)), "LoopInvPreservation") in
      (inv, loop_vc :: (vcs1 @ (exit_vc :: vcs0)))

  and wp_loop_context
      (inv : form) 
      (pre: command) 
      (test : form) 
      (post : command) 
      (f : form) : (form * (form * string) list) =
    (* Loop desugars into:

       assert inv;
       havoc modified variables;
       assume inv;
       pre;
       ((assume test; post; assert inv; assume False) []
       (assume (not test)))
     *)
    let mod_vars = Util.union (Sast.modified_vars_of pre) (Sast.modified_vars_of post) in
    let exit_f = smk_impl ((smk_not test), f) in
    let f0, vcs0 = wp_rec post ((mk_comment "InvPreservation" inv), []) in
    let loop_f = smk_impl (test, f0) in
    let f1, vcs1 = wp_rec pre ((smk_and [loop_f; exit_f]), []) in
    let havoc_f = choose relevant_defs mod_vars (smk_impl (inv, f1)) in
    let f' = smk_and [mk_comment "InvHoldsInitially" inv; havoc_f] in
      (f', vcs1 @ vcs0) in
    wp_rec c (f, [])

let remove_old (f : form) : form =
  let mk_map (id : ident) =
    if (FormUtil.is_oldname id) then [(id, (Var (FormUtil.unoldname id)))]
    else [] in
  let m = List.flatten (List.map mk_map (fv f)) in
    subst m f

let wp_proc
    (prog : program)
    (impl : impl_module)
    (proc : proc_def)
    (phdr : proc_header)
    (concretization : specvar_def list)
    (infer : command option)
    (use_context : bool) : obligation list =
  let sm_name = impl.im_name in
  let spec = AstUtil.must_find_sm sm_name prog in
  let pos = { pos_class = spec.sm_name; pos_method = phdr.p_name; pos_place = "" } in
  let sm_defs = List.flatten (List.map Vcgen.get_defs prog.p_specs) in
  let relevant_defs = concretization @ impl.im_constdefs @ impl.im_vardefs @ sm_defs in
  let sm_vars = List.map AstUtil.name_of_vd spec.sm_spec_vars in
  let specvars_except = AstUtil.specvars_except sm_name prog in
  let im_vds = specvars_except @ impl.im_vars @ phdr.p_formals @ proc.p_locals in
  let im_vars = List.map AstUtil.name_of_vd im_vds in
  let concretized_post = Sast.concretized_post prog impl proc phdr proc.p_body in
  let concretized_pre = Sast.concretized_pre prog impl phdr in
  let mk_obligation = mk_obligation prog impl relevant_defs (sm_vars @ im_vars) pos in
  let wp = weakest_precondition prog impl proc concretized_post infer use_context 
    relevant_defs in
  let vcs =
    if (!CmdLine.sastVC) then
      let f, vcs = wp proc.p_body mk_true in
	((remove_old f), "InitialPartOfProcedure") :: vcs
    else
      let f, vcs = wp proc.p_body concretized_post in
	((smk_impl (concretized_pre, (remove_old f))), "InitialPartOfProcedure") :: vcs in
    (List.map mk_obligation vcs)
    
