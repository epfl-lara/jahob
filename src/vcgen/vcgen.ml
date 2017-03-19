(** Verification condition generator. *)

(* VC generation for a procedure can be factored into:
    1) computing the set of relevant abstract variable definitions
    2) desugaring procedure into pure guarded command language
       (includes inlining of procedure calls and concretization)
       (for this see sast.ml)
    3) doing VC computation on the guarded-command language
       taking variable dependencies into account

   VC generation for rep invariants and initial condition can also be factored
   if needed.

*)

open Common
open Ast
open AstUtil
open Form
open FormUtil
open Background
open Sast

(** Debug messages **)
let debug_lmsg = Debug.debug_lmsg (Debug.register_debug_module "Vcgen")

(** Formula corresponding to variable definition *)
let form_of_def ((v:ident),(f:form)) : form = 
  mk_comment (v ^ "_def") (mk_eq(mk_var v,f))

let get_public_ghostvars (sm : spec_module) (prog : program) : var_decl list =
  let is_ghost (vd : var_decl) = vd.vd_ghost in
    List.filter is_ghost sm.sm_spec_vars

(*--------------------------------------------------*)
(** Compute the conditions associated with the initial
    state of the module refined in given 'map' *)
(*--------------------------------------------------*)
let init_for 
    (varid : string)
    (f : form) : form =
  match f with
    | Binder(Lambda, ts, f1) ->
	(* expand lambda in field definition *)
	let params = List.map (fun (id,t) -> mk_var id) ts in
	  mk_foralls(ts,mk_eq(App(mk_var varid,params), f1))
    | _ -> mk_eq(mk_var varid, f)

let init_by_tf (id : ident) (tf : typeForm) : form list =
  let v = mk_var id in
    match tf with
      | TypeApp(TypeInt, []) -> [mk_eq(v, (mk_int 0))]
      | TypeApp(TypeBool, []) -> [mk_eq(v, mk_false)]
      | TypeApp(TypeObject, []) -> [mk_eq(v, mk_null)]
      | _ -> []

let init_of_vd (vd : var_decl) : form list =
  match vd.vd_init with
    | None -> init_by_tf vd.vd_name vd.vd_type
    | Some f -> [init_for vd.vd_name f]

let get_defs (sm : spec_module) : specvar_def list = 
  sm.sm_constdefs @ sm.sm_vardefs

let get_concretization (prog : program) (im : impl_module) : specvar_def list =
  let rec get_maps (maps : mapping list) (acc : mapping list) : mapping list =
    match maps with
      | [] -> acc
      | map::maps1 ->
	  if map.map_impl = im then
	    get_maps maps1 (map::acc)
	  else
	    get_maps maps1 acc
  in
    List.flatten (List.map (fun x -> x.map_abst) (get_maps prog.p_maps []))

let get_relevant_defs
    (concretization : specvar_def list)
    (im : impl_module)
    (prog : program) : specvar_def list =
  let smdefs = List.map get_defs prog.p_specs in
  let mydefs = List.concat 
    ([concretization; im.im_constdefs; im.im_vardefs] @ smdefs) in
  let myowned = impl_modules_claimed_by im prog in
  let owneddefs = 
    List.flatten
      (List.map 
	 (fun x -> 
	    (get_concretization prog x) @ x.im_constdefs @ x.im_vardefs)
	 myowned)
  in
    mydefs @ owneddefs

let vcs_of_initial_state
    (prog : program)
    (map : mapping) : obligation list = 
  let im = map.map_impl in
  let sm = map.map_spec in
  let concretization = map.map_abst in
  let pos = {
    pos_class = sm.sm_name;
    pos_method = "INIT";
    pos_place = "";
  } in 
  
    (** Maintaining the list of verification conditions *)
  let (vcs : obligation list ref) = ref [] in
  let oblig_of (msg : string) (f : form) = {
    ob_pos = pos;
    ob_purpose = msg;
    ob_form = f;
  } in   
  let add_vc_only (msg : string) (f : form) : unit =
    (vcs := oblig_of msg f :: !vcs) in    
  let add_vc (msg : string) (f : form) : unit =
    add_vc_only msg (add_background_form prog im f) in

  let repvar_decls = get_rep_vars im prog @ get_public_ghostvars sm prog in
  let get_vd_name vd = vd.vd_name in
  let _ = debug_lmsg 0 (fun () ->"INIT: rep var decls: " ^ 
		      String.concat ", " 
		      (List.map get_vd_name repvar_decls) ^ "\n") in
    
  let relevant_defs = get_relevant_defs concretization im prog in

  let defs_forms = List.map form_of_def relevant_defs in
  let rep_init_forms = List.concat (List.map init_of_vd repvar_decls) in
    
  let str_tree = "tree" in

  (** known_invs is a list of invariants that are known to hold in
      the initial state.  For example, we know that an empty heap
      forms a union of trees. *)
  let rec is_tree_inv (i : Specs.invariant_desc) : bool =
    match (FormUtil.strip_types i.Specs.inv_form) with
      | App (Var s, [App (Const ListLiteral, fields)]) when s=str_tree -> true
      | _ -> false
  in
  let known_invs : Specs.invariant_desc list = List.filter is_tree_inv im.im_invs in
  let _ = debug_lmsg 0 (fun () ->Printf.sprintf 
			"vcgen.vcs_of_initial_state: Total %d known_invs computed.\n" 
			(List.length known_invs)) in
  let alloc_init = [mk_eq(all_alloc_objsf, Jast.alloc_initial_value)] in
  let initial_rep_state_form = 
    mk_and (alloc_init @ (ListLabels.map ~f:Specs.good_looking_inv known_invs) @ rep_init_forms @ defs_forms) in

    (** check that abstraction function maps the initial values 
	of rep variables to initial values of abstract variables *)
  let check_initial_value (vd : var_decl) : unit = 
    match vd.vd_init with
      | None -> ()
      | Some finit ->
	  if not vd.vd_ghost then
	    add_vc ("initialValueFor" ^ vd.vd_name)
	      (mk_impl(initial_rep_state_form,
		       init_for vd.vd_name finit))
  in

    (** check that private invariants hold in the state given
	by initial values of rep variables. *)
  let check_private_invariant (inv : form) =
    add_vc "PrivateInvHoldsInitially"
      (mk_impl(initial_rep_state_form, inv))
  in

  let aspecvars = accessible_specvars prog im.im_name in
  let init_spec_state_form = 
    mk_and
      (List.concat (List.map init_of_vd aspecvars))
  in

  (** check that public invariants hold in the state given
      by initial values of public variables *)
  let check_public_invariant (inv : form) = 
    add_vc "PublicInvariantHoldsInitially"
      (mk_impl(init_spec_state_form, inv))
  in
    List.iter check_initial_value sm.sm_spec_vars;
    List.iter check_private_invariant (ListLabels.map ~f:Specs.good_looking_inv im.im_invs);
    List.iter check_public_invariant (ListLabels.map ~f:Specs.good_looking_inv sm.sm_invs);
    !vcs

(*--------------------------------------------------*)
(** Check that invariants are preserved by external operations,
    which are guaranteed not to change owned objects 

Invariant preservation for invariant k is something like:

    \bigwedge_k I_k &
    (ALL x. x.owner=C --> (\bigwedge_{f not private of C}  x.f = x.f'))
    --> I'_k

Spec variable preservation for variable v is something like:

    \bigwedge_k I_k &
    (ALL x. x.owner=C --> (\bigwedge_{f not private of C}  x.f = x.f')) -->
    def_v = def'_v

*)
(*--------------------------------------------------*)
let original_vcs_of_rep
    (prog : program)
    (map : mapping) : obligation list =
  let im = map.map_impl in
  let sm = map.map_spec in
  let smname = sm.sm_name in
  let defs = map.map_abst in
  let pos = {
    pos_class = smname;
    pos_method = "REP";
    pos_place = "";
  } in 
  
    (** Maintaining the list of verification conditions *)
  let (vcs : obligation list ref) = ref [] in
  let oblig_of (msg : string) (f : form) = {
    ob_pos = pos;
    ob_purpose = msg;
    ob_form = f;
  } in   
  let add_vc_only (msg : string) (f : form)  =
    (vcs := oblig_of msg f :: !vcs) in    
  let add_vc (msg : string) (f : form)  =
    add_vc_only msg (add_background_form prog im f) in

  let get_vd_name vd = vd.vd_name in
  let repvar_decls = get_rep_vars im prog in
  let aspecvars = accessible_specvars prog im.im_name in
  let externally_modifiable = 
    Util.difference 
      (List.map get_vd_name aspecvars)
      (List.map get_vd_name repvar_decls) in
  let _ = debug_lmsg 0 (fun () ->"REP: externally modifiable: " ^ 
		      String.concat ", " externally_modifiable ^ "\n") in
  let defs_forms = List.map form_of_def defs in
  let invs_forms = ListLabels.map ~f:Specs.good_looking_inv (im.im_invs @ sm.sm_invs) in
  let allinvs = mk_and (invs_forms @ defs_forms) in
  let fresh (id : ident) = id ^ "_after" in
  let mk_havoc_map (id : ident) : (ident * form) =
    (id, mk_var (fresh id)) in
  let havoc_map = List.map mk_havoc_map externally_modifiable in
  let mk_fieldeq (fname : ident) : form =
    mk_eq(mk_var fname,mk_var (fresh fname)) in
  let is_field (id : ident) =
    let rec search vds = match vds with
      | [] -> false
      | vd::vds1 when vd.vd_name = id -> vd.vd_field
      | vd::vds1 -> search vds1
    in search aspecvars in
  let externally_mod_fields = 
    List.filter is_field externally_modifiable in
  let fieldeqs = List.map mk_fieldeq externally_mod_fields in
  let xid = "framedObj" in
  let xvar = mk_var xid in
  let rep_preserved = 
    mk_forall(xid,mk_object_type,
	      mk_impl(mk_eq(mk_old_owner_of xvar,
			    mk_var (mk_class_token_name smname)),
		      mk_and fieldeqs)) in
  let alloc_monotonic = App (Const Subseteq, [mk_var "Object.alloc"; mk_var (fresh "Object.alloc")]) in
  let lhs = mk_and [alloc_monotonic; allinvs; rep_preserved] in

    (** check that private invariants is preserved *)
  let check_private_invariant (inv : Specs.invariant_desc) =
    add_vc ("Invariant_" ^ inv.Specs.inv_name ^"_PreservedByOutside")
      (mk_impl(lhs,subst havoc_map inv.Specs.inv_form)) in

    (** check that values of specification variables are preserved *)
  let check_specvar ((id,f) : specvar_def) = 
    add_vc ("PreservationOfVariable" ^ id ^ "ByOutside")
      (mk_impl(lhs,mk_eq(f,subst havoc_map f)))
  in
    (List.iter check_private_invariant im.im_invs;
     List.iter check_specvar defs;
     !vcs)

let vcs_of_rep
    (prog : program)
    (map : mapping) : obligation list = []
  (* original_vcs_of_rep prog map *)

(* end vcs_of_rep *)

(** [defined_affected_by ids defs] computes the list of variables (from [ids]
    and the definitions [defs]) affected by the variables [ids] *)
let defined_affected_by (ids : ident list) (defs : specvar_def list) : ident list =
  let rec closure 
      (check_now : specvar_def list)
      (check_later : specvar_def list)
      (dependent : ident list) : ident list =
    match check_now with
      | [] -> dependent
      | (id,f)::check_now1 ->
	  if Util.disjoint dependent (fv f) then
	    closure check_now1 ((id,f)::check_later) dependent
	  else
	    closure (check_now1 @ check_later) [] (id::dependent)
  in
  let _ = debug_lmsg 0 (fun () ->"\nInput of affected_by:" ^ String.concat ", " ids ^ "\n") in
  let res = closure defs [] ids in
  let _ = debug_lmsg 0 (fun () ->"\nOutput of affected by:" ^ String.concat ", " res ^ "\n") in
    res

let always_false _ = false
let always_true _ = true

(** Enrich postcondition with definitions of variables *)
let assume_dependencies
    (relevant_defs : (ident * form) list)  (** definitions of all relevant specification variables *)
    (xs : string list) (** variables whose dependencies we should make explicit *)
    (f : form) (** postcondition being enriched *)
    : form (** postcondition enriched with definitions *) =
  let txs = Util.remove_dups (defined_affected_by xs relevant_defs) in
  let _ = debug_lmsg 0 (fun () ->"Variables affected by " ^ String.concat "," xs ^ " are: " ^ String.concat ", " txs ^ "\n") in
  let mk_def_eq (id : ident) : form option =
    try
      let fid = List.assoc id relevant_defs in
	Some (mk_comment (id ^ "_def") (mk_eq(mk_var id,fid)))
    with Not_found -> 
      if List.mem id xs then None
      else 
	(Util.warn ("\n vcgen.choose: [Internal] Could not resolve affected variable" ^ id ^ "\n"); 
	 None) in
  let rec apply_defs (go : bool)
      (current_ids : ident list) (ids : ident list) 
      (formula : form) : form =
    match current_ids with
      | [] -> 
	  if go then apply_from_start ids formula
	  else formula
      | id::cids1 ->
	  (if List.mem id (fv formula) then
	     match mk_def_eq id with
	       | Some fd -> 
		   apply_defs true cids1 ids (mk_impl (fd,formula))
	       | None -> 
		   apply_defs go cids1 (id::ids) formula
	   else 
	     apply_defs go cids1 (id::ids) formula)
  and apply_from_start ids formula =
    apply_defs false ids [] formula
  in
    apply_from_start txs f
(*
    smk_impl_def_eq FormUtil.lambda_or_no_binder (smk_and affected_id_def_forms,f)
*)
    
(** The essence of vcgen with specification variables:
      we want to havoc variables 'xs' in postcondition f 
      (these 'xs' variables can be specvars defined in terms of others).
    To do this, we first make their definitions explicit using 'assume_dependencies',
    and then rename them.  We also return the renaming substitution.
*)
let choose_with_deps 
    (relevant_defs : (ident * form) list)  (** definitions of specification variables *)
    (xs : string list) (f : form) : 
    (form (** resulting postcondition *) 
     * substMap (** renaming into fresh variables *)) =
  let txs = defined_affected_by xs relevant_defs in
  let _ = debug_lmsg 0 (fun () ->"Variables affected by " ^ String.concat "," xs ^ " are: " ^ String.concat ", " txs ^ "\n") in
  let mk_sub (x:ident) : ident * form = 
    (x, mk_var (Util.fresh_name x)) in
  let (sub : substMap) = List.map mk_sub txs in
  let f0 = assume_dependencies relevant_defs xs f in
    (subst sub f0, sub)

(* -------------------------------------------------*)
(** Computing weakest precondition of basic command *)
(* -------------------------------------------------*)
let wp_bc 
    (prog : program) 
    (im : impl_module)
    (p : proc_def)
    (ph : proc_header)
    (concretization : specvar_def list)
    (vcs_opt : obligation list ref option) = 
  let smname = im.im_name in
  let sm = must_find_sm smname prog in
  let pos = {
    pos_class = sm.sm_name;
    pos_method = ph.p_name;
    pos_place = "";
  } in 
    
  let get_name vd = vd.vd_name in
  let names_of_locals = List.map get_name p.p_locals in
  let sm_vars = List.map get_name sm.sm_spec_vars in
  let im_vars = 
    List.map get_name (specvars_except smname prog) @
    List.map get_name im.im_vars @
    List.map get_name ph.p_formals @
    names_of_locals in

  let relevant_defs = (** definitions of specification variables *)
    get_relevant_defs concretization im prog in

  (** implicit universal quantification, models nondeterministic choice.
      Because we do not substitute dependent variables elsewhere, 
      we now havoc dependent variables and
      add equalities expressing their definitions to the formula.
  *)
  let choose (xs : string list) (f : form) : form =
    let (f_res,_) = choose_with_deps relevant_defs xs f in
      f_res
  in

  let complete_deps (f : form) : form =
    assume_dependencies relevant_defs (sm_vars @ im_vars) f 
  in 
    
  (** Assignment statement *)
  let choose_assign (x : ident) (e : form) (f : form) : form =
    let (f_res,sub) = choose_with_deps relevant_defs [x] f in     
    let xnew = (* find what 'x' was renamed to *)
      (try List.assoc x sub
       with Not_found -> (Util.warn "[Internal] vcgen.choose_assign"; mk_var x))
    in  
      smk_impl_def_eq always_true (mk_eq(xnew, e), f_res)
  in

  let havoc (rs : form list) (f : form) : form =
    choose (List.concat (List.map region_to_id rs)) f in

  let oblig_of (msg : string) (f : form) = {
    ob_pos = pos;
    ob_purpose = msg;
    ob_form = f;
  } in   
  let add_vc_only vcs (msg : string) (f : form)  =
    (vcs := oblig_of msg f :: !vcs) in    
  let add_vc (msg : string) (f : form)  =
    match vcs_opt with
    | Some vcs -> add_vc_only vcs msg (complete_deps (add_background_form prog im f))
    | None -> ()
  in

  let wp_alloc x t f =
    (* havoc x;
       assume x ~: alloc_t;
       alloc_t := alloc_t Un {x}
    *)
    let xf = mk_var x in
    let rhs = mk_cup (all_alloc_objsf, mk_singleton xf) in
    let f1 = choose_assign all_alloc_objs rhs f in
    let x_type = mk_elem(xf,mk_var (obj_var t)) in
    let x_nin_alloc = mk_notelem(xf,all_alloc_objsf) in
    let x_nonnull = mk_neq(xf,mk_null) in
    let f2 = smk_impl(smk_and [x_nonnull; x_nin_alloc; x_type;
			       get_unalloc_lonely_xid prog x], f1) in
      choose [x] f2 in

  let wp_array_alloc x t ds f =
    (* x = new T[d1];

         becomes

       havoc x;
       assume x in alloc_array
       assume x .. array.length = s;
       alloc_array := alloc_array Un {x};
    *)
    match ds with
      | d1::ds1 ->
	  let _ = (if ds1 <> [] then 
		     Util.warn "vcgen.wp_array_alloc: multidim array"
		   else ()) in
	  let xf = mk_var x in
	  let rhs = mk_cup (all_alloc_objsf, mk_singleton xf) in
	  let f1 = choose_assign all_alloc_objs rhs f in
	  let x_nonnull = mk_neq(xf,mk_null) in
	  let x_nin_alloc = mk_notelem(xf,all_alloc_objsf) in
	  let x_length = mk_eq(mk_arrayLength xf,d1) in
	  let f2 = smk_impl(smk_and [x_nonnull;x_nin_alloc;
				 get_unalloc_lonely_xid prog x;
				    x_length], f1) in
	    choose [x] f2
      | [] -> 
	  Util.warn "vcgen.wp_array_alloc: array with no dimensions";
	  f
  in

  let wp_proc_call (pc : proc_call) (f : form) : form = 
    mk_comment "ProcedureCallNotDesugared" mk_false in

  let wp_bc1 (bc : basic_command) (f : form) : form =
    match bc with
      | Skip -> f
      | VarAssign{assign_lhs=x;assign_rhs=e} -> 
	  (debug_lmsg 0 (fun () ->"\nApplying assignment substitution [" ^ x ^ " -> " ^ PrintForm.string_of_form e ^ 
		      "] to formula" ^ PrintForm.string_of_form f ^"\n");
	   choose_assign x e f)
	   (* FormUtil.subst [(x,e)] f *)
      | Alloc{alloc_lhs=x;alloc_type=t} -> wp_alloc x t f
      | ArrayAlloc{arr_alloc_lhs=lhs;arr_alloc_type=t;arr_alloc_dims=ds} ->
	  wp_array_alloc lhs t ds f
      | Assert{hannot_form=e;hannot_msg=m;hannot_hints=hints} ->  
	  smk_and [mk_hint_comment hints m e;f]
      | NoteThat{hannot_form=e;hannot_msg=m;hannot_hints=hints} ->  
	  smk_and [mk_hint_comment hints m e;smk_impl(mk_comment m e,f)]
      | Assume{annot_form=e;annot_about=None; annot_msg=m} -> 
	  smk_impl(mk_comment m e, f)
      | Assume{annot_form=e;annot_about=Some v;annot_msg=m} -> 
	  smk_impl_if_relevant v (mk_comment m e, f)
      | Split{annot_form=e;annot_msg=m} -> 
	  (add_vc ("SPLIT_" ^ m) (smk_impl(e,f));
	   e)
      | Havoc{havoc_regions=rs} -> havoc rs f
      | ProcCall pc -> wp_proc_call pc f
      | Hint _ -> f
      | Instantiate _ ->
	  Util.fail "wp_bc1: uncaught pattern matching case 'Instantiate'"
      | Mp _ -> 
	  Util.fail "wp_bc1: uncaught pattern matching case 'Mp'"
 in wp_bc1


(* ---------------------------------------------*)
(** Computing proof obligations for a procedure *)
(* ---------------------------------------------*)

let vcs_of_procedure
    (prog : program)
    (im : impl_module)
    (p : proc_def)
    (ph : proc_header)
    (concretization : specvar_def list)
    (use_context : bool) (** use info about unmodified parts of state at loops *)
    : obligation list =
  let smname = im.im_name in
  let sm = must_find_sm smname prog in
  let pos = {
    pos_class = sm.sm_name;
    pos_method = ph.p_name;
    pos_place = "";
  } in 
    
  let get_name vd = vd.vd_name in
  let names_of_locals = List.map get_name p.p_locals in
  let sm_vars = List.map get_name sm.sm_spec_vars in
  let im_vars = 
    List.map get_name (specvars_except smname prog) @
      List.map get_name im.im_vars @
      List.map get_name ph.p_formals @
      names_of_locals in

  (*  let conjoin_concretize = conjoin_concretize prog im in *)

  let relevant_defs = get_relevant_defs concretization im prog in

  (** implicit universal quantification, models nondeterministic choice.
      Because we do not substitute dependent variables elsewhere, 
      we now havoc dependent variables and
      add equalities expressing their definitions to the formula.
  *)
  let choose (xs : string list) (f : form) : form =
    let (f_res,_) = choose_with_deps relevant_defs xs f in
      f_res
  in

  (** Add all state dependencies to a formula representing state.
      It should always be sound, but is needed when having the final verification condition.
      This does not do a havoc.
  *)
  let complete_deps (f : form) : form =
    assume_dependencies relevant_defs (sm_vars @ im_vars) f 
  in 

  (** Maintaining the list of verification conditions *)
  let (vcs : obligation list ref) = ref [] in

  let oblig_of (msg : string) (f : form) = {
    ob_pos = pos;
    ob_purpose = msg;
    ob_form = f;
  } in   
  let add_vc_only (msg : string) (f : form)  =
    (vcs := oblig_of msg f :: !vcs) in    
  let add_vc (msg : string) (f : form)  =
    add_vc_only msg (complete_deps (add_background_form prog im f)) in

  (** precondition of currently analyzed procedure *)
  let concretized_pre = concretized_pre prog im ph in
  let _ = debug_lmsg 0 (fun () ->"\nConcretized pre: " ^ PrintForm.string_of_form concretized_pre) in

  (** postcondition of currently analyzed procedure *)
  let concretized_post = concretized_post prog im p ph p.p_body in 

  let wp_bc = wp_bc prog im p ph concretization (Some vcs) in

  let rec wp_loop_plain
      (inv : form) (s1 : command) (cond : form) (s2 : command)
      (f : form) : form =
    let concretized_inv = inv in
    let _ = Debug.msg
      ("\nConcretized inv:\n" ^ 
	 PrintForm.string_of_form concretized_inv ^
	 "\n") in
      (* inv => wp(s1;assume cond;s2, inv) *)
    let _ = Debug.msg
      ("\nwp s2 concretized_inv:\n" ^ 
	 PrintForm.string_of_form (wp s2 concretized_inv) ^
	 "\n") in
      add_vc "LoopInvPreservation"
	(smk_impl(concretized_inv,
		  wp s1
		    (smk_impl(cond,
			      wp s2 concretized_inv))));
      (* inv => wp(s1;assume (not cond), f) *)
      add_vc "LoopInvImpliesPost"
	(smk_impl(concretized_inv,
		  wp s1
		    (smk_impl(mk_not cond,f))));
      concretized_inv

  and wp_loop_context (* takes into account unmodified properties before loop *)
      (inv : form) (s1 : command) (cond : form) (s2 : command)
      (f : form) : form =
    (*
      Desugaring of loop 

      assert inv;
      havoc vars;
      assume inv;
      s1;
      ((assume cond; s2; assert inv; assume False) []
      (assume (not cond)))

      --> (postcondition f)

      inv & choose mods (
      inv => wp(s1,f1 & f2)
      )
      
      f1: cond => wp(s2, inv)
      f2: not cond => f
    *)
    let mods = Util.remove_dups 
      ((modified_vars_of s1) @ (modified_vars_of s2)) in
    let cinv = inv in
    let f1 = smk_impl(cond,wp s2 (mk_comment "InvPreservation" cinv)) in
    let f2 = smk_impl(mk_not cond,f) in
      smk_and [mk_comment "InvHoldsInitially" cinv;
	       choose mods (smk_impl(cinv, wp s1 (smk_and [f1; f2])))]
  and wp1 (c : command) (f : form) : form =
    (* Also accumulates vcs to global variable as a side effect *)
    match c with
      | Basic{bcell_cmd = bc} -> wp_bc bc f
      | Seq cs -> List.fold_right wp cs f
      | Choice cs -> smk_and (List.map (fun c1 -> wp c1 f) cs)
      | If{if_condition=cond;if_then=thenc;if_else=elsec} ->
	  smk_and [smk_impl(cond,wp thenc f);
		   smk_impl(mk_not cond, wp elsec f)]
      | Loop{loop_inv=oinv;loop_prebody=s1;loop_test=cond;loop_postbody=s2} ->
	  (match oinv with
	     | None -> (debug_lmsg 0 (fun () -> "loop without loop invariant");
			mk_comment "NoLoopInvGiven" mk_false)
	     | Some inv ->
		 (debug_lmsg 0 (fun () -> "\nCHECKING LOOP.\n");
		  if use_context then
		    wp_loop_context inv s1 cond s2 f
		  else
		    wp_loop_plain inv s1 cond s2 f
		 ))
      | Return {return_exp=fo} ->
	  let res = 
	    (match fo with
	       | None -> concretized_post
	       | Some f1 -> subst [(result_var,f1)] concretized_post) in
	    mk_comment "ReturnStatement" res
      | PickAny _ -> (debug_lmsg 0 (fun () -> "pick any not desugared");
			mk_comment "PickAnyNotDesugared" mk_false)
      | PickWitness _ -> (debug_lmsg 0 (fun () -> "pick witness not desugared");
			mk_comment "PickWitnessNotDesugared" mk_false)
      | Assuming _ -> Util.fail "wp1: uncaught pattern matching case 'Assuming'"
      | Induct _ -> Util.fail "wp1: uncaught pattern matching case 'Induct'"
      | Contradict _ -> Util.fail "wp1: uncaught pattern matching case 'Contradict'"
      | Proof _ -> Util.fail "wp1: uncaught pattern matching case 'Proof'"

  and wp (c : command) (f : form) : form =
    let res = wp1 c f in
      (debug_lmsg 0 (fun () -> "\n\nc:\n" ^ PrintAst.pr_command c ^"\n");
       debug_lmsg 0 (fun () -> "f:\n" ^ PrintForm.string_of_form f ^"\n");
       debug_lmsg 0 (fun () -> "\nwlp c f = " ^ PrintForm.string_of_form res ^"\n");
       res)
  in 
  let direct_vc () = 
    let _ = Util.msg("Using direct VC generation.\n") in
    let wpre = wp p.p_body concretized_post in
      (add_vc "InitialPartOfProcedure"
	 (mk_impl(concretized_pre, remove_old wpre)));
      !vcs
  in
    if !CmdLine.sastVC then
      (let c = p.p_body in
       let _ = Util.msg("Using VC generation from simplified Ast.\n") in
       let wpre = wp c mk_true in
	 add_vc "" (remove_old wpre);
	 !vcs)
    else 
      direct_vc()
