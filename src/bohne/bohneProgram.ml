open Util
open Ast
open AstUtil
open Form
open FormUtil
open TypeReconstruct
open TermRewrite
open Slice
open PrintForm
open BohneUtil
open BohnePred

(** Commands in a Bohne program *)
type guarded_command = {
    mutable gc_havoc : form list;
    mutable gc_guard : form;
    mutable gc_command : basic_command list
  }

(** Control flow nodes of a Bohne program *)
type location = {
    loc_pp : program_point;
    mutable loc_cmds : (guarded_command * program_point) list;
    mutable loc_preds : pred_decl list;
    mutable loc_split_preds : pred_decl list;
    mutable loc_invariants : form list;
    mutable loc_assertions : (guarded_command * form) list
  }

(** Bohne programs *)
type bohne_program = {
    program_name : string;
    locations : (int, location) Hashtbl.t;
    entry_point : program_point;
    exit_point : program_point;
    wp : (basic_command list -> form -> form);
    global_env : typedIdent list;
    mutable idents : ident list;
    post_ghost_vars : (typedIdent * form) list;
    vardefs : (ident * form) list;
    assumed_invariants : form list;
    background : form list;
    mutable initial_states : form
  }

let gc_skip () = {gc_havoc = []; gc_guard = mk_true; gc_command = []}

let initial_location program =
  Hashtbl.find program.locations program.entry_point.pp_id

let is_initial_pp program pp =
  program.entry_point.pp_id = pp.pp_id 

let is_exit_pp program pp =
  program.exit_point.pp_id = pp.pp_id 

let get_location program pp =
  Hashtbl.find program.locations pp.pp_id

let no_loops_reachable program pp =
  let rec ae_exit seen = function
    | [] -> true
    | pp :: todo ->
       let loc = get_location program pp in
       if List.mem pp seen && loc.loc_cmds != [] then false else
       let todo' = List.fold_left (fun todo' (_, succ_pp) -> succ_pp :: todo') todo loc.loc_cmds
       in ae_exit (pp :: seen) todo'
  in ae_exit [] [pp] 

let on_cycle program pp =
  let succs pp todo = 
    let loc = get_location program pp in
    List.fold_left (fun todo' (_, succ_pp) -> succ_pp :: todo') todo loc.loc_cmds
  in
  let rec oc seen = function
    | [] -> false
    | pp' :: todo ->
	pp.pp_id = pp'.pp_id ||
	if List.mem pp' seen then oc seen todo else
	oc (pp' :: seen) (succs pp' todo)
  in oc [] (succs pp [])

let project_gc_havoc gc =
  match gc.gc_havoc with
  | [] -> []
  | h -> [Havoc {havoc_regions = h; 
		 havoc_msg=""; 
		 havoc_constraint=None;
		 havoc_internal=false}] 

let elim_gc_havoc program gc =
  let subst_map, havoc_assigns = List.fold_left
      (fun (sm, ha) f -> 
	let x, ty =
	  match f with
	  | Var x -> x, TypeUniverse 
	  | TypedForm (Var x, ty) -> x, ty
	  | f -> failwith ("unsupported havoc region in BohneProgram.remove_gc_havoc: " ^ string_of_form f)
	in
	let fresh_x = Util.fresh_name x in
	let rhs = TypedForm (Var fresh_x, ty) in
	program.idents <- fresh_x :: program.idents;
	(x, rhs) :: sm, 
	VarAssign {assign_lhs = x; assign_tlhs = (x, ty); assign_rhs = rhs} :: ha)
      ([], []) gc.gc_havoc 
  in
  {gc_havoc = []; gc_guard = subst subst_map gc.gc_guard; gc_command = gc.gc_command @ havoc_assigns}


let gc_to_basic_commands gc =
  let havocs = project_gc_havoc gc in
  let havoc_assumes = 
    List.fold_left (fun acc f -> 
      Assume {annot_form = f; annot_about = None; annot_msg = ""} :: acc) 
      havocs (split_conjuncts gc.gc_guard) 
  in gc.gc_command @ havoc_assumes

let compose program gc1 gc2 =
  assert (gc2.gc_havoc = []);
  {gc_havoc = gc1.gc_havoc;
   gc_guard = smk_and [gc1.gc_guard; program.wp gc1.gc_command gc2.gc_guard];
   gc_command = gc2.gc_command @ gc1.gc_command}

let print_command chan pp (gc, pp') =
  let out s = output_string chan s in
  out (Printf.sprintf "Location %d -> Location %d\n" pp.pp_id pp'.pp_id);
  List.iter (fun c -> out (PrintAst.pr_basic_cmd c)) (List.rev (gc_to_basic_commands gc));
  out "\n"
  
let object_vars_from_gc gc =
  List.fold_left 
    (fun acc c -> match c with
    | VarAssign ac -> 
	let object_vars = free_object_vars ac.assign_rhs in
	Util.union acc object_vars
    | _ -> acc) [] gc.gc_command


let print_program chan program =
  let out s = output_string chan s in
  let locations = 
    List.sort 
      (fun l1 l2 -> compare l1.loc_pp.pp_id l2.loc_pp.pp_id) 
      (Hashtbl.fold (fun _ l acc -> l :: acc) program.locations [])
  in
  let print_predicates l =
    out (Printf.sprintf "Location %d\n" l.loc_pp.pp_id);
    List.iter (print_pred_decl chan) l.loc_preds;
    out "\n"
  in  
  let print_transitions l =
    List.iter (print_command chan l.loc_pp) l.loc_cmds
  in
  let out_line () = out (String.make 80 '*' ^ "\n") in
  out "\n";
  out_line ();
  out ("Bohne program " ^ program.program_name ^ "\n");
  out_line ();
  out "\n";
  out (Printf.sprintf "Precondition:\n\n%s\n\n" 
	 (string_of_form (smk_metaand (split_conjuncts program.initial_states))));
  out (Printf.sprintf "Initial location: %d\n\n" program.entry_point.pp_id);
  out (Printf.sprintf "Final location: %d\n\n" program.exit_point.pp_id);
  out "Transitions:\n\n";
  List.iter print_transitions locations;
  out_line ();
  out "\n";
  out "Predicates:\n\n";
  List.iter print_predicates locations;
  out_line ();
  out "\n"

(** Reachability relation between control flow nodes *)
let reaches program pp1 pp2 =
  let rec reaches pp1 pp2 seen =
    pp1.pp_id = pp2.pp_id ||
    try 
      let loc1 = get_location program pp1 in 
      List.exists (fun (_, pp) -> 
	not (List.mem pp.pp_id seen) &&
	reaches pp pp2 (pp.pp_id::seen)) loc1.loc_cmds
    with Not_found -> false
  in reaches pp1 pp2 [pp1.pp_id]

(** Total order on control flow nodes *)
let compare_pps program pp1 pp2 =
  if pp1.pp_id = pp2.pp_id then 0 else
  let r_21 = reaches program pp2 pp1 
  and r_12 = reaches program pp1 pp2 in
  if r_21 && not r_12 then 1
  else if r_12 && not r_21 then -1
  else compare pp2.pp_id pp1.pp_id

(** Propagate assert and assume statements 
 and remove commands with unsatisfiable guards *)
let propagate_asserts_assumes program =
  let mk_assert f = Assert {hannot_msg = ""; 
			    hannot_about = None; 
			    hannot_form = f; 
			    hannot_hints=[];
			    hannot_forSuch=[]} in
  let update_assert c (gc, f) =
      let _ = match c with
      |	Assume af ->
	  let f = 
	    if af.annot_msg = "" then af.annot_form 
	    else mk_comment af.annot_msg af.annot_form
	  in
	  gc.gc_guard <- smk_and [f; gc.gc_guard]
      |	Assert _ | Split _ -> ()
      |	_ -> 
	  gc.gc_guard <- negation_normal_form (mk_not (program.wp [c] (mk_not gc.gc_guard)));
	  gc.gc_command <- c::gc.gc_command
      in (gc, f)
  in
  let assumed_invariants = smk_and program.assumed_invariants in
  let background = smk_and program.background in
  let propagate pp cmds =
    let remove_asserted_postconds succ_pp =
      if not (is_exit_pp program succ_pp) then fun cmds -> cmds else
      let succ_loc = get_location program succ_pp in
      let postconds = List.concat (List.map (fun a -> split_conjuncts (snd a)) succ_loc.loc_assertions) in
      let rec remove acc = function
	| Assert af::cmds' ->
	    let asserts = split_conjuncts af.hannot_form in
	    (match List.filter (fun a -> not (List.exists (equal a) postconds)) asserts with
	    | [] -> remove acc cmds'
	    | rest -> 
		af.hannot_form <- smk_and rest;
		remove (Assert af :: acc) cmds')
	| cmds -> List.rev_append acc cmds
      in remove []
    in
    let check_c succ_pp (cmd', asserts, assumes) c =
      match c with
      |	Assume af ->
	   (* Remove assumptions which are just type annotations. 
	    * This makes the analysis significantly faster; should be done in a less dirty way.
	   if is_type_annot af then 
	     if not !CmdLine.background then
	       (cmd', asserts, assumes)
	     else (cmd', List.rev_map (update_assert c) asserts, mk_comment af.annot_msg af.annot_form::assumes)
	   else *)
	  (cmd', List.rev_map (update_assert c) asserts, 
	   (* mk_comment af.annot_msg *) af.annot_form :: assumes) 
      |	Assert af ->
	  let assrt = (gc_skip (), af.hannot_form) in
	  (cmd', assrt :: asserts, assumes)
      | NoteThat af ->
	  let assrt = (gc_skip (), af.hannot_form) in
	  (cmd', assrt :: List.rev_map (update_assert c) asserts,
	   af.hannot_form :: assumes)
      |	Split _ -> 
	  (cmd', asserts, assumes)
      |	_ -> (c :: cmd', List.rev_map (update_assert c) asserts, 
	      List.rev_map (fun f -> negation_normal_form (mk_not (program.wp [c] (mk_not f)))) assumes)
    in
    let propagate_gc (assertions, cmds') (cmd, succ_pp) =
      let cs, asserts, assumes = 
	List.fold_left (check_c succ_pp) ([], [], []) 
	  (remove_asserted_postconds succ_pp (mk_assert (smk_and program.assumed_invariants)::cmd.gc_command))
      in 
      let f = mk_impl (smk_and (background::assumed_invariants::assumes), mk_false) in
      if BfCachedDecider.decide_fast trivial_context f
      then (assertions, cmds') else begin
	cmd.gc_command <- List.rev cs;
	(* if is_initial_pp program pp then
	  cmd.gc_guard <- smk_and (program.initial_states::assumes)
	else *) cmd.gc_guard <- smk_and assumes;
	(List.fold_left (fun acc (gc, assn) -> 
	  gc.gc_havoc <- gc.gc_havoc @ cmd.gc_havoc; (gc, assn) :: acc)
	   assertions asserts, (cmd, succ_pp) :: cmds')
      end
    in
    List.fold_left propagate_gc ([], []) cmds
  in
  let propagate_initial_assumes () =
    let init_loc = initial_location program in
    let guards = List.rev_map (fun (gc, _) -> gc.gc_guard) init_loc.loc_cmds in
    let init = match guards with
    | g::guards' -> 
	let common_guards = List.fold_left (fun acc f ->
	  let fs = split_conjuncts f in
	  Util.intersect acc fs) (split_conjuncts g) guards'
	in common_guards
    | _ -> []
    in
    let _ = 
      List.iter 
	(fun (gc, _) ->
	  let guard_diff_init = Util.difference (split_conjuncts gc.gc_guard) init in
	  gc.gc_guard <- smk_and guard_diff_init)
	init_loc.loc_cmds
    in
    program.initial_states <- smk_and (program.initial_states::init)
  in
  let process_location _ loc =
    let assertions, cmds' = propagate loc.loc_pp loc.loc_cmds in
    List.iter (fun (gc, f) -> gc.gc_command <- List.rev gc.gc_command) assertions;
    loc.loc_assertions <- assertions @ loc.loc_assertions;
    loc.loc_cmds <- cmds'
  in 
  Hashtbl.iter process_location program.locations;
  propagate_initial_assumes ()

(** Eliminate all havoc statements that do not occur on loops *)
let eliminate_havocs program =
  let elim_havocs loc =
    let havoc_free_cmds = List.map (fun (gc, dst_pp) -> (elim_gc_havoc program gc, dst_pp)) loc.loc_cmds in
    loc.loc_cmds <- havoc_free_cmds
  in
  Hashtbl.iter (fun _ loc -> if not (on_cycle program loc.loc_pp) then
    	    elim_havocs loc) program.locations

(** Derive an initial set of predicates using various heuristics *)
let derive_initial_predicates program =
  (* let _ = print_string "idents: "; List.iter (Printf.printf "%s, ") program.idents; print_newline () in *)
  let prog_vars f0 =
    let f1 = normalize_form true f0 in
    let f, env = TypeReconstruct.reconstruct_types (get_annotated_types f1) f1 in
    let fs, g = sequent_of_form f in 
    let f = form_of_sequent 
	(List.filter (function | App (Const Comment, [c; _]) -> false | _ -> true) fs, g)
    in
    (* let seq = slice [slice_obj_vars; slice_obj_sets] env seq0 in *)
    let vars = List.fold_left 
	(fun vars x -> 
	  try let ty = List.assoc x env in
	  if not (is_oldname x) && 
	    (ty = mk_object_type ||ty = mk_bool_type || ty = mk_obj_set_type)
	  then (x, ty) :: vars else vars
	  with Not_found -> Util.warn ("missing type for variable " ^ x); vars) 
	[] (fv f)
    in
    vars
  in
  let add_var_preds pp_id vs =
    let l = Hashtbl.find program.locations pp_id in
    List.fold_left 
      (fun has_new_preds v ->
	if List.mem (fst v) program.idents && (fst v) <> "Object" then
	  let v_pred = add_var_pred_decl l.loc_pp v in
	  if not (in_preds v_pred l.loc_preds)
	  then (l.loc_preds <- v_pred :: l.loc_preds; true)
	  else has_new_preds
	else has_new_preds)
      false vs
  in
  let get_updated assertion_map = List.fold_left
      (fun updated (pp_id, assns) ->
	let vs = List.fold_left 
	    (fun vs f -> union vs (prog_vars f)) 
	    [] assns
	in
	(* let _ = Printf.printf "%d: " pp_id in 
	let _ = List.iter (fun v -> Printf.printf "%s, " (fst v)) vs; print_newline () in *)
	let has_new_preds = add_var_preds pp_id vs in
	if has_new_preds then pp_id::updated else updated)
      [] assertion_map
  in
  let next_assertion_map assertion_map updated =
    let new_assns l = List.fold_left 
	(fun new_assns (c, pp') ->
	  if List.mem pp'.pp_id updated then
	    let assns' = List.map 
		(fun f -> 
		  normalize_form true (program.wp (gc_to_basic_commands c) f))
		(List.assoc pp'.pp_id assertion_map)
	    in List.rev_append assns' new_assns
	  else new_assns) 
	[] l.loc_cmds
    in
    Hashtbl.fold (fun pp_id l assertion_map' ->
      match new_assns l with
      |	[] -> assertion_map'
      |	assns -> (pp_id, assns) :: assertion_map')
      program.locations []
  in
  let rec derive_var_preds assertion_map =
    match assertion_map with
    | [] -> ()
    | _ -> 
	let updated = get_updated assertion_map in
	let assertion_map' = next_assertion_map assertion_map updated in
	derive_var_preds assertion_map'
  in 
  let initial_assertion_map = 
    Hashtbl.fold
      (fun pp_id l assertion_map -> 
	if not (empty l.loc_assertions) then
	  let expanded_assns = 
	    List.rev_map 
	      (fun (gc, f) ->
		let f0 = program.wp (gc_to_basic_commands gc) f in
		let f1 = normalize_form true f0 in
		fst (rewrite true [rewrite_tree] [] f1))		 
	      l.loc_assertions 
	  in
	  (pp_id, expanded_assns) :: assertion_map
	else assertion_map) 
      program.locations []
  in
  let derive_iterators () =
    let check_iterator pp cmds acc p_decl =
      try 
	let p, ty = 
	  find_map 
	    (function IsSingleton opt -> opt | _ -> None) 
	    p_decl.pred_props
	in
	let x1 = Util.fresh_name "x" in
	let x2 = Util.fresh_name "x" in
	let updates = List.fold_left (fun updates (gc, pp') ->
	  if pp.pp_id <> pp'.pp_id then updates
	  else match normalize 2 (program.wp gc.gc_command (mk_var p)) with
	  | App (Const Impl, [_; App (Const FieldRead, [f; Var p'])])
	  | App (Const FieldRead, [f; Var p']) when p = p' -> 
	      let f = mk_eq (App (f, [mk_var x1]), mk_var x2) in
	      f :: updates
	  | _ -> updates) [] cmds
	in 
	match updates with 
	| [] -> acc 
	| _ ->
	    let iter_form =
	      App (mk_var str_rtrancl, 
		   [Binder (Lambda, [(x1, ty); (x2, ty)], smk_or updates);			   
		    mk_var p; mk_var x1])
	    in
	    let iter_def = Binder (Comprehension, [(x1, ty)], iter_form) in
	    let iter_decl = add_pred iter_def [Inherit [pp]]
	    in iter_decl :: acc
      with _ -> acc
    in
    Hashtbl.iter
      (fun pp_id l ->
	let var_preds = List.filter is_singleton l.loc_preds in
	let iter_preds = List.fold_left 
	    (check_iterator l.loc_pp l.loc_cmds) [] var_preds
	in l.loc_preds <- union_preds iter_preds l.loc_preds)
      program.locations
  in
  derive_var_preds initial_assertion_map;
  if !BohneOptions.opt_derive_iterators then derive_iterators ();
  if !BohneOptions.opt_abstract_final then 
    Hashtbl.iter (fun _ loc ->
      List.iter (fun (gc, dst_pp) ->
	List.iter (function | TypedForm (Var v, TypeApp (TypeObject, [])) -> 
	  let dst_loc = get_location program dst_pp in
	  let v_pred = add_var_pred_decl dst_pp (v, mk_object_type) in
	  dst_loc.loc_preds <- union_preds [v_pred] dst_loc.loc_preds
	  | _ -> ()) gc.gc_havoc) loc.loc_cmds) program.locations;
  let init =
    let init_loc = initial_location program in
    let type_annot = Str.regexp "\\(.*tmp.*\\)_type$" in
    List.filter 
      (function
	| App (Const Comment, [Const StringConst c; _]) when Str.string_match type_annot c 0 ->
	    let v = Str.matched_group 1 c in
	    List.exists (fun p -> List.exists (fun (v', _) -> v = v') p.pred_env) init_loc.loc_preds
	| _ -> true
      ) (split_conjuncts program.initial_states)
  in
  program.initial_states <- smk_and init

let add_split_preds program pp_id split_preds =
  let loc = get_location program pp_id in
  loc.loc_split_preds <- union_preds loc.loc_split_preds split_preds
  
