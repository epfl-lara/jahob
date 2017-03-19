open Util
open Form
open FormUtil
open PrintForm
open BohneUtil
open BohnePred
open BohneProgram
open BohneRegion
open Ast
open Bf
open Bf_set
open BohneAbstraction
open CachedDecider
open BfCachedDecider
open BohneRefine

(* debug messages *)
let debug_msg = Debug.debug_print_msg (Debug.register_debug_module "Bohne")

let total_fix_iterations = ref 0
let total_refinement_steps = ref 0

(** Abstract initial states *)
let abstract_init region invs init =
  let preds = region.preds in
  let var_preds = List.filter is_singleton preds in
  let abs_init0, init = List.fold_left 
      (fun (abs_init, init) f ->
	let abs_f = fast_alpha preds [] f in
	if 
	  entails_fast trivial_context (smk_and [invs; gamma false preds abs_f]) f && 
	  entails_fast trivial_context (smk_and [invs; f]) (gamma false preds abs_f)
	then begin
	  Bf_set.inter abs_init abs_f, init
	end
	else abs_init, f :: init) 
      (Bf_set.top, []) (split_conjuncts init)
  in
  let init = smk_and init in
  (* let _ = print_form init in
  let _ = print_abs_states stdout abs_init0 in *)
  let abs_init1 = alpha preds (Bf_set.join abs_init0, stack_context preds) invs init in
  let abs_init = Bf_set.conj abs_init0 abs_init1 in
  let _ = debug_msg 3 (fun chan -> 
    output_string chan "\nbefore coerce:\n"; 
    print_abs_states chan abs_init)
  in
  let abs_init = coerce true preds preds trivial_context (smk_and [init; invs]) abs_init in 
  let abs_init = List.fold_left (fun acc p ->
    if is_old p then
      let new_p = unold_pred p in
      Bf_set.conj acc (Bf.equi (Bf.mk_var p.pred_index) (Bf.mk_var new_p.pred_index))
    else acc) abs_init preds in
  let final_abs_init =
    if (*true ||*) !BohneOptions.opt_no_splitting then abs_init else
    let _ = debug_msg 3 (fun chan -> 
      output_string chan "before splitting:\n"; 
      print_abs_states chan abs_init;
      output_string chan "after splitting:") 
    in
    let split_abs_init0 = 
      if true || !BohneOptions.opt_no_splitting then abs_init
      else split_equalities var_preds abs_init
    in
    if !BohneOptions.opt_refine then split_abs_init0
    else coerce !BohneOptions.opt_extra_precise preds preds trivial_context (mk_and [init; invs]) split_abs_init0
  in
  let _ = debug_msg 1 (fun chan -> 
    Debug.newline ();
    print_abs_states chan final_abs_init) 
  in final_abs_init


(** Make root region of ART *)
let mk_root_region entry_location assumed_invs init =
  let preds = entry_location.loc_preds in
  let invs = smk_and assumed_invs in
  let root_region = mk_root_region entry_location.loc_pp preds assumed_invs init in
  let abs_init = abstract_init root_region invs init in
  let _ = root_region.absstates <- abs_init in
  root_region

let havoc_vars havocs f =
  let havoced_vars = get_annotated_types (mk_list havocs) in
  let havoc_sub = List.map (fun (v, _) -> (v, mk_var (v ^ "_havoced"))) havoced_vars in
  subst havoc_sub f


(** Abstract post operator *)
let abstract_post =
  (* cache for abstract weakest preconditions *)
  let pred_upd_map : (Bf.t * Bf.t) FormHashtbl.t = FormHashtbl.create 0 in
  fun extra_precise lfp region' wp ->
    let gc, new_abs_states0, parent = region'.parent in
    let region = !parent in
    let guard = gc.gc_guard in
    let _ = debug_msg 2 (fun chan ->
      output_string chan "\nComputing abstract post for command:\n";
      print_command chan region.ppoint (gc, region'.ppoint);
      Printf.fprintf chan "Source region is: %d\n" region.timestamp;
      Printf.fprintf chan "Successor region is: %d\n" region'.timestamp;
      flush chan)
    in
    if Bf_set.le new_abs_states0 Bf_set.bottom  (* ||
    equal gc.gc_guard mk_true && gc.gc_havoc = [] && gc.gc_command = [] *)
    then new_abs_states0 else
      let havoced_vars = get_annotated_types (mk_list gc.gc_havoc) in
      let havoc_preds = 
	List.fold_left (fun acc (x,ty as xt) -> 
	  if (ty = mk_object_type || ty = mk_obj_set_type) &&
	    List.mem x (fv gc.gc_guard) 
	  then add_var_pred_decl region'.ppoint xt :: acc
	  else acc) [] havoced_vars 
      in 
      let is_havoced_form =
	let hvs = List.map fst havoced_vars in
	fun f -> intersect hvs (fv f) <> []
      in
      let is_havoced p = is_havoced_form p.pred_def in
      let preds' =
	region'.preds <- union_preds havoc_preds region'.preds;
	let relevant_preds = 
	  List.filter (fun p -> not (inherits p) || inherits_to region'.ppoint p) region'.preds 
	in
	sort_preds relevant_preds
      in 
      let preds = 
	let relevant_preds =
	  List.filter (fun p -> not (inherits p) || inherits_to region.ppoint p) region.preds 
	in
	sort_preds (union_preds (List.filter is_singleton havoc_preds) relevant_preds) in
      (* let _ = print_endline "Preds" in
      let _ = List.iter (print_pred_decl stdout) preds in
      let _ = print_endline "Preds'" in
      let _ = List.iter (print_pred_decl stdout) preds' in *)
      let project_havoced_preds = 
	let nonhavoced = (List.filter (fun p -> not (is_havoced p)) preds) in
	Bf_set.map (restrict_preds false nonhavoced)
      in 
      let wp f = normalize_form false (wp gc.gc_command f) in

      let abs_guard = fast_alpha region.preds [] gc.gc_guard in
      
      let guarded_abs_states =
	(* let may_sat_guard = Bf_set.filter 
	  (fun absstate -> 
	    satisfiable trivial_context
	      inv_guard (stack_context region.preds absstate)) region. *)
	let guarded_abs_states0 = find_in_lfp lfp region.ppoint.pp_id guard in
	(* let guarded_abs_states1 = Bf_set.inter !parent.absinvariant guarded_abs_states0 in *)
	let guarded_abs_states2 = fast_prune region.preds (Bf_set.inter abs_guard guarded_abs_states0) in
	project_havoced_preds ((*Bf_set.inter !parent.absinvariant*) guarded_abs_states2)
      in

      (* prepare abstract states for which post is computed *)
      let new_abs_states = 
	let new_abs_states0 = project_havoced_preds new_abs_states0 in
	let new_abs_states1 = 
	  if !BohneOptions.opt_refine_progress 
	  then Bf_set.inter region.absinvariant new_abs_states0 
	  else new_abs_states0
	in
	let new_abs_states3 = fast_prune region.preds (Bf_set.inter abs_guard new_abs_states1) in
	let new_abs_states4 = 
	  if !BohneOptions.opt_refine_progress then 
	    congruence_closure preds new_abs_states3 
	  else new_abs_states3
	in
	new_abs_states4
      in

      let invariants = havoc_vars gc.gc_havoc (smk_and region.invariant) in
      let inv_guard = smk_and [invariants; guard] in
      let _ = debug_msg 3 (fun chan -> 
	output_string 
	  chan 
	  ("Invariants:\n" ^ 
	   string_of_form (havoc_vars gc.gc_havoc (smk_metaand region.invariant))
	   ^ "\n"))
      in 

      let get_wp_pred p wp_p =
	if not !BohneOptions.opt_no_splitting && is_singleton p then 
	  let def_wp_p = Binder (Comprehension, typed_free_var_list 1, wp_p) in
	  add_pred def_wp_p []
	else List.find (fun p' -> FormUtil.equal (pred_to_form true p') wp_p) preds
      in
      let mk_wp_pred p wp_p =
	let def_wp_p = 
	  if is_state_pred p then wp_p
	  else Binder (Comprehension, typed_free_var_list p.pred_arity, wp_p) in
	add_pred def_wp_p p.pred_props
      in
      let refinement_support = support_preds region.absinvariant in
      let input_support = 
	if !BohneOptions.opt_fast_abstraction then preds
	else support_preds new_abs_states 
      in
      
      (* determine the set of context predicates that are useful for abstraction of [f0] *)
      let get_context_preds f0 =
	if not !BohneOptions.opt_use_instantiation then preds else
	let f = form_of_sequent (elim_fv_in_seq false (sequent_of_form f0)) in
	let object_vars = free_object_vars f in
	List.filter (fun p -> 
	  try 
	    let v = Util.find_map (function IsSingleton x -> x | _ -> None) p.pred_props in
	    List.mem (fst v) object_vars
	  || in_preds p refinement_support
	  with Not_found -> true) preds
      in
      
      (* the actual abstract post computation *)
      let abstract_post source_states0 context_states =
	let source_states = (* fast_prune region.preds source_states0 *)
	  (* prune_empty region.preds trivial_context guard *) source_states0
	in
	if Bf_set.le source_states Bf_set.bottom then Bf_set.bottom else
	let _ = debug_msg 3 (fun chan ->
	  output_string chan "Context:\n"; 
	  print_abs_state chan (Bf_set.join context_states))
	in
 
        (* compute the context for given set of context predicates *)
	let mk_context context_preds =
	  if !BohneOptions.opt_use_instantiation then
	    if not !BohneOptions.opt_use_context then
	      (Bf.top, fun _ -> mk_true)
	    else 
	      (Bf_set.join context_states, 
	       fun abs_state ->
		 smk_and [stack_context context_preds abs_state;
			  (*concretize_state_invariant context_preds abs_state;*)
			  gamma false context_preds !parent.absinvariant])
	  else 
	    (Bf_set.join source_states, gamma_state false preds)
	in
	
        (* computes predicate update for given predicate *)
	let rec compute_pred_update p i' preds =
	  let def_p = pred_to_form true p in
	  let wp_p0 = wp def_p in
	  let context_fun f = mk_context (get_context_preds f) in
	  let context = context_fun wp_p0 in
	  let concr_context = (snd context) (fst context) in
	  let _ = debug_msg 2 (fun chan -> 
	    Printf.fprintf chan "Process predicate %s\nwp(%s) = %s\n\n" 
	      p.pred_name p.pred_name (PrintForm.string_of_form (wp_p0))) in
	  let dep_preds = get_deps p in
          (* first recursively compute updates of dependant predicates... *)
	  let dep_updates = 
	    List.rev_map 
	      (fun dep_pname ->
		let dep_p = pred_by_name dep_pname in
		let wp_dep_p = normalize_form false (wp (pred_to_form true dep_p)) in
		let dep_p' = mk_wp_pred dep_p wp_dep_p in
		let dep_p_upd = compute_pred_update dep_p (Bf.mk_var dep_p'.pred_index) preds in
		let relevant_context = project_unknown (support_preds (Bf_set.singleton dep_p_upd)) (fst context) in
		let update = Bf.conj dep_p_upd relevant_context in
		gamma_state false (union_preds [dep_p'] preds) update)
	      dep_preds
	  in
          (* ...then compute update of p itself *)
	  let relevant_preds = List.filter (fun p' ->
	    (in_preds p' refinement_support && is_singleton p' || 
	    is_relevant (smk_impl (guard, wp_p0)) p') && 
	    not (Util.empty (Util.intersect p.pred_dep_vars p'.pred_dep_vars)) &&
            ((*not !BohneOptions.opt_fast_abstraction ||*) 
	     not (is_havoced p' && eq_preds p p'))) preds
	  in
	  let wp_p = mk_impl (smk_and (inv_guard :: dep_updates), wp_p0) in
	  let wp_notp = mk_impl (smk_and (inv_guard :: dep_updates), wp (smk_not def_p)) in
	  let key = 
	    let key0 = mk_list ((*normalize_form false*) (smk_impl (concr_context, wp_p)) :: 
	      (List.map (fun p -> pred_to_form true p) (sort_preds relevant_preds)))
	    in 
	    PersistentCache.alpha_rename key0
	  in
	  let abs_wp_p, abs_wp_notp =
	    try FormHashtbl.find pred_upd_map key 
	    with Not_found ->
	      let res =
		if (* !BohneOptions.opt_fast_abstraction && *) is_state_pred p then
		  if BfCachedDecider.decide_fast context wp_p then
		    Bf.top, Bf.bottom
		  else if BfCachedDecider.decide_fast context wp_notp then
		    Bf.bottom, Bf.top
		  else Bf.bottom, Bf.bottom
		else if !BohneOptions.opt_fast_abstraction && equal wp_p0 def_p && in_preds p input_support && not (is_havoced p) 
	                || is_old p || has_prop IsConst p
		then 
		  Bf.mk_var p.pred_index, Bf.neg (Bf.mk_var p.pred_index)
		else 
		  let abs_wp_p, abs_wp_notp =
		    if (is_havoced_form wp_p0 || not (in_preds p input_support)) && !BohneOptions.opt_fast_abstraction then
		      try
			fast_uabstract_form relevant_preds (mk_context relevant_preds) invariants (*p*) wp_p  
		      with Failure _ -> Bf.bottom, Bf.bottom
		    else Bf.bottom, Bf.bottom
		  in
		  if Bf.le abs_wp_p Bf.bottom && Bf.le abs_wp_notp Bf.bottom then
		    uabstract_form relevant_preds context_fun wp_p wp_notp false 
		  else abs_wp_p, abs_wp_notp
	      in 
	      (* there seems to be a soundness issue related to caching of
		 context-dependent predicate updates
              if not !BohneOptions.opt_use_context then *)
	      FormHashtbl.add pred_upd_map key res;
	      res
	  in 
	  let _ = debug_msg 3 (fun chan -> 
	    Printf.fprintf chan "wp^#(%s) = \n" (p.pred_name); 
	    print_cubes chan abs_wp_p;
	    Printf.fprintf chan "wp^#(~%s) = \n" (p.pred_name); 
	    print_cubes chan abs_wp_notp;
	    Debug.newline ())
	  in
	  let _ = if !BohneOptions.opt_check_soundness then
	    let context = mk_context preds in
	    let tobechecked = smk_impl (gamma_objs false relevant_preds abs_wp_p, wp_p0) in
	    assert (entails context inv_guard tobechecked);
	    let tobechecked = smk_impl (gamma_objs false relevant_preds abs_wp_notp, wp (smk_not def_p)) in
	    assert (entails context inv_guard tobechecked)
	  in
	  let pred_upd = 
	    Bf.conj (Bf.impl (abs_wp_p) i')
	      (Bf.impl (abs_wp_notp) (Bf.neg i'))
	  in 
	  pred_upd
	in

        (* compute abstract transition relation for context and given command *)
        (* split_preds': predicates that are used for splitting
         * ext_preds: freshly introduced predicates that represent weakest preconditions 
         *            of predicates in region'  
         * split_rel: transition relation that relates split_preds' with predicates in region'
         * upd_preds: predicates in region' for which updates still have to be computed 
         * trans_rel: transition relation that relates ext_preds with predicates in region' *)
	let split_preds', ext_preds, split_rel, upd_preds, abs_trans_rel0 =
	  let process_pred (split_preds, ext_preds, split_rel, upd_preds, trans_rel) p =
	    let def_p = pred_to_form true p in
	    let wp_p = normalize_form false (wp def_p) in
	    let i' = Bf.mk_primed_var p.pred_index in
	    let split_preds', ext_preds', split_update, upd_preds', pred_update = 
	      try
		let p' = if has_prop IsConst p then p else get_wp_pred p wp_p in
		let split_preds' = 
		  if (is_havoced p' && is_singleton p') || in_preds p region'.split_preds then
		    union_preds [p'] split_preds
		  else split_preds
		in
		let ext_preds', split_update = 
		  if in_preds p' split_preds || 
	          not (is_havoced p') && 
		  !BohneOptions.opt_fast_abstraction &&
		  (* in_preds p' input_support && *)
		  (true || not (is_singleton p') || not (in_preds p region'.split_preds))
		  then 
		    ext_preds, Bf.top
		  else 
		    union_preds [p'] ext_preds, 
		    compute_pred_update p (Bf.mk_var p'.pred_index) preds
		in 
		(split_preds', ext_preds', split_update, upd_preds, Bf.equi (Bf.mk_var p'.pred_index) i')
	      with Not_found ->
     		if (not (is_havoced_form wp_p) || not !BohneOptions.opt_fast_abstraction) &&
                  (* in_preds p input_support && *) (true || in_preds p preds || is_state_pred p)
		then 
		  (split_preds, ext_preds, Bf.top, union_preds [p] upd_preds, Bf.top)
		else
		  let p' = mk_wp_pred p wp_p in
		  (split_preds, union_preds [p'] ext_preds, 
		   compute_pred_update p (Bf.mk_var p'.pred_index) preds, upd_preds, 
		   Bf.equi (Bf.mk_var p'.pred_index) i')
	    in
	    (split_preds', ext_preds', Bf.conj split_rel split_update, 
	     upd_preds', Bf.conj trans_rel pred_update)
	  in
	  List.fold_left process_pred ([], [], Bf.top, [], Bf.top) preds' 
	in 
	
	let ext_preds = List.filter 
	    (fun p -> not (is_havoced p) ||
	    List.mem p.pred_index (Bf.dom split_rel)) ext_preds 
	in
	let all_preds = union_preds ext_preds preds in
	let abs_trans_rel = 
	  let preds = union_preds preds split_preds' in
	  let abs_trans_rel1 = List.fold_left (fun abs_trans_rel p ->
	    let i' = Bf.mk_primed_var p.pred_index in
	    Bf.conj abs_trans_rel (compute_pred_update p i' preds))
	      Bf.top upd_preds
	  in Bf.conj abs_trans_rel0 abs_trans_rel1
	in

        (* split abstract states *)
	let _ = debug_msg 3 (fun chan ->
	  output_string chan "Split predicates: ";
	  List.iter (fun p -> output_string chan (p.pred_name ^ " ")) split_preds';
	  Debug.newline ();
	  output_string chan "Extended predicates:\n";
	  List.iter (print_pred_decl stdout) ext_preds;
	  Debug.newline ();
	  output_string chan "All predicates:\n";
	  List.iter (print_pred_decl stdout) all_preds;
	  Debug.newline ())
	in    
	let abs_states = 
	  let context = mk_context preds in
	  let refined_abs_states0 = Bf_set.conj source_states split_rel in
	  let refined_abs_states1 = Bf_set.conj refined_abs_states0 (project_unknown all_preds (Bf.neg !empty_cubes)) in
	  let refined_abs_states = 
	    if extra_precise then 
	      coerce !BohneOptions.opt_extra_precise ext_preds all_preds context
		inv_guard ((*split (List.filter is_state_pred split_preds')*) refined_abs_states1)
            else (* prune_empty all_preds context inv_guard*) refined_abs_states1
	  in
	  let split_abs_states = 
	    if (* true || *) !BohneOptions.opt_no_splitting || empty split_preds' 
	    then refined_abs_states
	    else split split_preds' refined_abs_states 
	  in
	  let _ =
      	    (* check whether we did anything brain damaged *)
	    if !BohneOptions.opt_check_soundness then
	      let _ = debug_msg 3 (fun chan ->
		output_string chan "Source states: \n";
		print_abs_states chan source_states;
		output_string chan "Split relation: \n";
		print_abs_states chan (Bf_set.singleton split_rel);
		output_string chan "refined_abs_states0: \n";
		print_abs_states chan refined_abs_states0;
		output_string chan "refined_abs_states1: \n";
		print_abs_states chan refined_abs_states1;
		output_string chan "Split states: \n";
		print_abs_states chan split_abs_states)
	      in
	      (* let tobechecked = smk_impl (gamma false all_preds source_states, gamma false all_preds refined_abs_states0) in
		 assert (entails trivial_context inv_guard tobechecked);
		 let tobechecked = smk_impl (gamma false all_preds source_states, gamma false all_preds refined_abs_states1) in
		 assert (entails trivial_context inv_guard tobechecked); *)
	      let tobechecked = smk_impl (gamma false all_preds source_states, gamma false all_preds split_abs_states) in
	      assert (entails trivial_context inv_guard tobechecked)
	  in
	  congruence_closure preds (fast_prune ext_preds split_abs_states)
	in

	let _ = debug_msg 3 (fun chan ->
	  output_string chan "Final input states:\n"; 
	  print_abs_states chan abs_states)
	in

        (* compute abstract post of final input states *)
	let abs_post =
	  Bf_set.map 
	    (fun abs_state ->
	      debug_msg 4
		(fun chan -> 
		  output_string chan "Transition Relation:\n"; 
		  print_cubes chan ((* Bf.conj abs_state *) abs_trans_rel));
	      let post = Bf.rel_prod abs_state abs_trans_rel in
	      debug_msg 4
		(fun chan ->
		  output_string chan "Output state:\n"; 
		  print_abs_state chan post);
	      post) abs_states
	in 
        (*let tobechecked = smk_impl (gamma false all_preds region'.absstates, gamma false all_preds region'.absinvariant) in
           assert (entails trivial_context (smk_and region'.invariant) tobechecked); *)
	let _ = debug_msg 3 (fun chan ->
	  output_string chan "Final output states:\n"; 
	  print_abs_states chan abs_post)
	in abs_post
      in
      let post_states =
	if !BohneOptions.opt_context_per_state then
	  Bf_set.fold (fun post_states abs_state ->
	    let sabs_state = Bf_set.singleton abs_state in
	    let abs_post = abstract_post sabs_state sabs_state in
	    Bf_set.union abs_post post_states) Bf_set.bottom new_abs_states
	else 
	  (* Bf_set.fold (fun post_states guard_state ->
	    let abs_post = abstract_post (Bf_set.conj new_abs_states guard_state) (Bf_set.singleton guard_state) in
	    Bf_set.union abs_post post_states) Bf_set.bottom guarded_abs_states *)
	  abstract_post new_abs_states guarded_abs_states
      in 
      if false && !BohneOptions.opt_refine_progress then Bf_set.inter region'.absinvariant post_states else post_states

let project_dead_vars program region abs_states_in =
  let loc = get_location program region.ppoint in
  let common_havoced = 
    if List.length loc.loc_cmds > 0 then
      List.fold_left (fun common_havoced (gc, _) ->
	let havoced = List.fold_left (fun acc ->
	  function 
	    | Var v
	    | TypedForm(Var v, _) -> v :: acc
	    | _ -> acc) [] gc.gc_havoc
	in
	Util.intersect common_havoced havoced) program.idents loc.loc_cmds
    else []
  in
  let havoced_preds = List.filter (fun p -> 
    let fvs = fv p.pred_def in
    not (Util.empty fvs) && 
    not (Util.empty (Util.intersect fvs common_havoced))) region.preds
  in
  let havoced_vars = List.map (fun p -> p.pred_index) havoced_preds in
  let abs_states_out =
    Bf_set.fold (fun acc abs_state ->
      Bf_set.add acc (Bf.exists havoced_vars abs_state)) Bf_set.bottom abs_states_in
  in
  abs_states_out
  
(** Compute least fixed point *)
let fix program root_region =
  let module Pq = 
    PriorityQueue(struct 
      type el = region 
      type context = bohne_program
      let equal = region_equal	
      let compare prog r1 r2 =
	let _, _, r1_parent = r1.parent in
	let _, _, r2_parent = r2.parent in
	let res = compare_pps prog !r1_parent.ppoint !r2_parent.ppoint in
	if res = 0 then 
	  let res = compare_pps prog r1.ppoint r2.ppoint in
	  if res = 0 then compare r2.timestamp r1.timestamp
	  else res
	else res
    end) in
  let lfp = Hashtbl.create (Hashtbl.length program.locations) in
  let insert = Pq.insert program in
  let insert_top = Pq.insert_top program in
  let extract = Pq.extract program in
  let remove = Pq.remove program in
  let assumed_invs = program.assumed_invariants in
  let insert_succs unprocessed region =
    let invariants = smk_and region.invariant in
    let loc = Hashtbl.find program.locations region.ppoint.pp_id in
    let restrict_to_guard gc =
      let inv_guard = smk_and [invariants; havoc_vars gc.gc_havoc gc.gc_guard] in
      let may_sat_guard = Bf_set.filter 
	  (fun absstate -> 
	    satisfiable trivial_context
	      inv_guard (stack_context region.preds absstate))
	  region.absstates
	  (* (Bf_set.inter region.absstates abs_guard) *)
      in

      (* update fixpoint data structure *)
      let _ = update_lfp_by_guard lfp region.ppoint.pp_id gc.gc_guard may_sat_guard in
      may_sat_guard
    in
    (* create successor region for given guarded command *)
    let create_succ_region (gc_with_havoc, succ_pp) =
      let gc = (* elim_gc_havoc program *) gc_with_havoc in
      let succ_loc = get_location program succ_pp in
      let succ_preds = 
	union_preds 
	  (if !BohneOptions.opt_abstract_final && is_exit_pp program succ_pp 
	  then List.filter is_singleton region.preds else [])
	  succ_loc.loc_preds 
      in
      let succ_invs = assumed_invs @ succ_loc.loc_invariants in
      let succ_absstates = restrict_to_guard gc in      
      let _ = add_preds_to_lfp lfp succ_pp.pp_id succ_preds in
      let succ_region = mk_succ region gc succ_pp succ_preds succ_loc.loc_split_preds succ_absstates succ_invs in
      succ_region
    in
    let unprocessed' = List.fold_left 
	(fun unprocessed' (gc, succ_pp) ->
	  if no_loops_reachable program succ_pp && not !BohneOptions.opt_abstract_final
	  then begin
	    ignore (update_lfp_by_guard lfp region.ppoint.pp_id gc.gc_guard region.absstates);
	    unprocessed'
	  end 
	  else insert unprocessed' (create_succ_region (gc, succ_pp)))
	unprocessed loc.loc_cmds
    in 
    let _ = match loc.loc_cmds with 
    | [] -> ignore (update_lfp_by_guard lfp region.ppoint.pp_id mk_true region.absstates)
    | _ -> ()
    in
    unprocessed'
  in
  (* check all assertions for current region and refine abstraction if necessary *)
  let check_and_insert_succs unprocessed region =
    match BohneRefine.check program region with
    | Some (region', has_new, new_preds, new_inherited_preds)
        (* found spurious error trace starting in [region'] *) ->
        (* remove subtree from region graph and recompute lfp *)
	  (* let _ = read_line () in *)
	  let remove_unprocessed unproc r =
	    remove (fun r' -> is_parent r r') unproc
	  in
        (* insert refined region in list of unprocessed regions *)
	let _ = 
	  let split_preds, preds = 
	    List.partition (fun p -> is_singleton p || is_state_pred p) new_preds in
	  if not has_new then 
	    (* if diff_preds support region'.split_preds = [] then *)
	    begin 
	      print_endline "\nDeadlock in refinement detected. Abort analysis.";
	      (* print_abs_states stdout region'.absstates; *)
	      flush_all ();
	      exit 1
	    end
	    (* else 
	      let _ = Util.amsg " (r2)"; incr total_refinement_steps in
	      region'.split_preds <- union_preds region'.split_preds support *)
	  else begin
	    let _ = Util.amsg " (r)"; incr total_refinement_steps in
	    add_preds lfp region' new_preds;
	    if not !BohneOptions.opt_lazy_abstraction then begin
	      let loc = get_location program region'.ppoint in
	      loc.loc_preds <- union_preds loc.loc_preds new_preds
	    end;
	    region'.inherited_preds <- union_preds region'.inherited_preds new_inherited_preds;
	    if not !BohneOptions.opt_no_splitting then begin
	      region'.split_preds <- union_preds region'.split_preds split_preds;
	      add_split_preds program region'.ppoint split_preds
	    end
	  end
	in 
	let unprocessed' = remove_subtree remove_unprocessed unprocessed region' in
	let uncovered_regions = recompute_lfp region'.timestamp lfp root_region in
	(* recompute initial state abstraction if refined region is root of ART *)
	if is_root region' then
	  let abs_init = abstract_init region'
	      (smk_and (program.background @ assumed_invs)) program.initial_states 
	  in 
	  region'.absstates <- abs_init; 
	  insert_top (List.fold_left insert_succs unprocessed' uncovered_regions) region'
	else insert_top unprocessed' region'
    | None (* no error trace found *) ->
        (* insert successors of [region] into list of unprocessed regions *)
	insert_succs unprocessed region
  in
  (* compute abstract states for region [region] and update list of unprocessed regions *)
  let compute_post region unprocessed =
    let extra_precise = 
      !BohneOptions.opt_extra_precise || 
      !BohneOptions.opt_abstract_final && is_exit_pp program region.ppoint
    in
    let _ = region.preds <- union_preds (get_location program region.ppoint).loc_preds region.preds in
    let post_states0 = abstract_post extra_precise lfp region program.wp in
    let post_states = project_dead_vars program region post_states0 in
    let covered, _ = project_lfp_by_guard lfp region.ppoint.pp_id mk_true in
    if Bf_set.le post_states covered then begin
      region.subsumed <- true;
      region.absstates <- post_states;
      unprocessed 
    end else
      (* let new_absstates = Bf_set.diff post_states covered in
      let _ = region.absstates <- new_absstates in *)
      let _ = region.absstates <- post_states in 
      let _ = update_lfp lfp region.ppoint.pp_id (* new_absstates *) post_states in
      check_and_insert_succs unprocessed region 
  in
  (* fix point computation loop *)
  let rec fix unprocessed =
    if unprocessed = Pq.empty then lfp else
    let region, unprocessed = extract unprocessed in
    let unprocessed' = compute_post region unprocessed in 
    let _ = Util.amsg " (f)"; incr total_fix_iterations in
    fix unprocessed'
  in
  (* initialize list of unprocessed regions *)
  let region_queue = check_and_insert_succs Pq.empty root_region in
  fix region_queue


(** Analyze program *)
let analyze program =
  let entry_location = Hashtbl.find program.locations program.entry_point.pp_id in
  let _ = reset_stats () in
  let start_time = 
    let ptime = Unix.times () in
    ptime.Unix.tms_utime +. ptime.Unix.tms_cutime  
  in
  let print_post_stats root_region lfp =
    let total_time = 
      let ptime = Unix.times () in
      ptime.Unix.tms_utime +. ptime.Unix.tms_cutime -. start_time
    in 
    let art_size, art_depth, total_preds, total_local_preds, max_local_preds =
      region_tree_stats root_region
    in
    let avrg_num_abs_states = lfp_stats lfp in
    let avrg_local_preds = float total_local_preds /. float art_size in
    let dp_stats = stats ()
    and _ = reset_stats () in
    let max_row = max_row_length () in
    let total_dp_rel_time = dp_stats.total_time /. total_time *. 100.0 in
    let dp_rel_time = dp_stats.total_dp_time /. total_time *. 100.0 in
    let coerce_dp_calls = !coerce_total_dp_calls + !split_total_dp_calls in
    let coerce_dp_time = !coerce_dp_time +. !split_dp_time in
    let coerce_dp_rel_time = coerce_dp_time /. total_time *. 100.0 in
    let abstract_dp_calls = dp_stats.calls - !refine_total_dp_calls in
    let abstract_dp_time = dp_stats.total_time -. !refine_dp_time in
    let abstract_dp_rel_time = abstract_dp_time /. total_time *. 100.0 in
    let refine_dp_rel_time = !refine_dp_time /. total_time *. 100.0 in
    let dp_rel_cache_hits = float dp_stats.cache_hits /. float dp_stats.calls *. 100.0 in
    let stats = "\nSTATISTICS\n" ^
      "Predicates:\n" ^
      Printf.sprintf "  # of predicates in total: %d\n" (List.length total_preds) ^
      Printf.sprintf "  avrg. # of local predicates: %.2f\n" avrg_local_preds ^
      Printf.sprintf "  max. # of local predicates: %d\n" max_local_preds ^
      "\nAbstract reachability tree (ART):\n" ^
      Printf.sprintf "  # of fixed point iterations: %d\n" !total_fix_iterations ^
      Printf.sprintf "  # of refinement steps: %d\n" !total_refinement_steps ^
      Printf.sprintf "  size of final ART: %d\n" art_size ^
      Printf.sprintf "  depth of final ART: %d\n" art_depth ^
      Printf.sprintf "  avrg. # of Boolean heaps per location: %.2f\n" avrg_num_abs_states ^
      "\nRunning time:\n" ^
      Printf.sprintf "  running time for analysis: %.2fs (100%%)\n" total_time ^ 
      Printf.sprintf "  time spent in reasoning backend: %.2fs (%.2f%%)\n" 
	dp_stats.total_time total_dp_rel_time ^
      Printf.sprintf "  time spent in DPs: %.2fs (%.2f%%)\n" dp_stats.total_dp_time dp_rel_time ^
      Printf.sprintf "  avrg. running time for single DP call: %.3fs\n" 
	(dp_stats.total_time /. float_of_int (dp_stats.calls - dp_stats.cache_hits)) ^
      Printf.sprintf "  max. running time for single DP call: %.3fs\n" dp_stats.max_time ^
      "\nDecision procedures (DPs):\n" ^
      Printf.sprintf "  # of VC calls in total: %d (%d DP calls, %.2fs)\n" 
	dp_stats.calls (dp_stats.calls - dp_stats.cache_hits) dp_stats.total_time ^
      Printf.sprintf "  # of VC calls for abstract post: %d (%.2fs, %.2f%%)\n" 
	abstract_dp_calls abstract_dp_time abstract_dp_rel_time ^
      Printf.sprintf "  # of VC calls for coerce: %d (%.2fs, %.2f%%)\n" 
	 coerce_dp_calls coerce_dp_time coerce_dp_rel_time ^
      Printf.sprintf "  # of VC calls for refinement: %d (%.2fs, %.2f%%)\n" 
	!refine_total_dp_calls !refine_dp_time refine_dp_rel_time ^
      Printf.sprintf "  # of cache hits in persistent cache: %d\n" 
	(!PersistentCache.valid_cache_hits + !PersistentCache.invalid_cache_hits) ^
      Printf.sprintf "  total cache hit ratio: %.2f%%\n" dp_rel_cache_hits ^
      Printf.sprintf "  max. cache row length: %d\n" max_row ^
      "\nMeasured function:\n" ^
      Printf.sprintf "  # calls: %d\n" !Util.measured_calls ^
      Printf.sprintf "  accumulated time: %.2fs\n"  !Util.measured_time 
      (* Printf.sprintf "  most expensive query:\n%s\n" (string_of_form dp_stats.max_query) *)
    in
(*    let _ = 
      print_endline "\nVC stats";
      Printf.printf "%s & %d & %d & %.2f\\%% & %.2f\\%% & %.2f\\%% & %.2f\\%% & %.3f & %.3f \\\\ \n"
	program.program_name
	dp_stats.calls 
	(dp_stats.calls - dp_stats.cache_hits)
	dp_rel_cache_hits
	total_dp_rel_time
	abstract_dp_rel_time
	refine_dp_rel_time
	(dp_stats.total_time /. float_of_int (dp_stats.calls - dp_stats.cache_hits))
	dp_stats.max_time;
      print_endline "\\hline\n";
      print_endline "\nART stats";
      Printf.printf "%s & %d & %d & %d & %d & %.2f & %d & %.1f & %d \\\\ \n"
	program.program_name
	!total_fix_iterations
	!total_refinement_steps
	art_size
	art_depth
	avrg_num_abs_states
	(List.length total_preds)
	avrg_local_preds
	max_local_preds;
	print_endline "\\hline\n"
    in *)
    Util.msg stats;
    if !BohneOptions.opt_print_art then
      let art_chan = open_out !BohneOptions.opt_art_file in
      print_region_tree art_chan root_region;
      close_out art_chan
  in

  let assumed_invariants = program.background @ program.assumed_invariants in
  let _ = phase "Precomputing empty cubes" 
      (fun () -> 
        debug_msg 2 (fun chan -> Debug.newline (); print_cubes chan !empty_cubes))
      ()
  in 
  let root_region = phase "Computing initial abstract states"
      (mk_root_region entry_location assumed_invariants) (subst program.vardefs program.initial_states)
  in
  let lfp = phase "Computing least fixed point"
      (fix program) root_region
  in 
  let _ = if !BohneOptions.opt_abstract_final then
    debug_msg 1
      (fun chan ->
	let exit_states, _ = project_lfp_by_guard lfp program.exit_point.pp_id mk_true in
	(* let exit_states = coerce preds (smk_and root_region.invariants) exit_states0 in *)
	output_string chan "\nFinal abstract states:\n";
	print_abs_states chan exit_states)
  in 
  (* let _ = print_cache stdout in *)
  print_post_stats root_region lfp;
  lfp, root_region
