open BohneUtil
open BohneProgram
open Bf
open Bf_set
open BohnePred
open Form
open FormUtil

(* debug messages *)
let debug_msg = Debug.debug_print_msg (Debug.register_debug_module "BohneAbstraction")


let entails_fast context f g =
  let f_impl_g = smk_impl (f, g) in
  BfCachedDecider.decide_fast context (concretize_preds f_impl_g)

let entails context f g =
  let f_impl_g = smk_impl (f, g) in
  BfCachedDecider.decide context (concretize_preds f_impl_g)

let measured_entails total_calls cached_calls acc_time context f g =
  let f_impl_g = smk_impl (f, g) in
  measured_decide_fast total_calls cached_calls acc_time context (concretize_preds f_impl_g)

let measured_entails_fast = measured_entails

let satisfiable context guard f =
  let not_f = smk_impl (smk_and (guard::get_all_defs ()), smk_not f) in
  not (BfCachedDecider.decide_fast context not_f)


(* maximal length of cubes *)
let max_cube_length = ref 2
	
let set_max_cube_length n = 
  max_cube_length := n

let print_cubes outchan cs =
  Bf.print outchan get_pred_name cs
    
let print_abs_state = print_cubes
    
let print_abs_states outchan abs_states =
  Bf_set.print outchan get_pred_name abs_states
 
let support_preds abs_states =
  let support_vars = Bf_set.dom abs_states in
  List.map get_pred_decl support_vars
  
let abstract_unknown fn preds bf =
  let preds_to_indices = List.map 
      (fun p -> p.pred_index)
  in
  let unknown = Util.difference 
      (preds_to_indices (get_all_preds ())) 
      (preds_to_indices preds)
  in fn unknown bf

let project_unknown preds bf =
  abstract_unknown Bf.exists preds bf

let forall_unknown preds bf =
  abstract_unknown Bf.forall preds bf
  
let restrict_preds project_old preds bf =
  let projected = List.fold_left 
      (fun acc p ->
	if is_old p && project_old || not (in_preds p preds)
	then p.pred_index::acc
	else acc) [] (get_all_preds ())
  in Bf.exists projected bf
    

let project_old_preds preds bf =
  let old_preds = List.fold_left 
      (fun acc p ->
	if is_old p then p.pred_index::acc
	else acc) 
      [] preds 
  in Bf.exists old_preds bf

    
let cubes_to_form =
  let create_cube preds c =
    let pos f = f in
    let neg f = smk_not f in
    let cube = List.fold_left
	(fun cube p -> 
	  if Bf.index_of_cube c (Bf.var_index p.pred_index) = 0 then 
	    neg (pred_to_form false p)::cube 
	  else if Bf.index_of_cube c (Bf.var_index p.pred_index) = 1 then 
	    pos (pred_to_form false p)::cube
	  else cube) [] preds 
      in 
      mk_and cube
  in 
  fun project_old preds abs_obj ->
    let preds =
      if project_old then List.filter (fun p -> not (is_old p)) preds
      else preds
    in
    let convert_cube acc c =
      create_cube preds c :: acc
    in
    let cubes = Bf.fold_cubes convert_cube [] abs_obj in
    smk_or cubes
    
type bf_tree = Leaf of bool | Node of Bf.var * bf_tree * bf_tree

let bf_tree_of_abs_obj preds abs_obj =
  let rec add_cube c tree = function
    | [] -> Leaf true
    | p :: preds' -> 
	let ec, tc = match tree with
	| Leaf _ -> Leaf false, Leaf false
	| Node (_, ec, tc) -> ec, tc
	in 
	if Bf.index_of_cube c (Bf.var_index p.pred_index) = 0 then
	  Node (p.pred_index, add_cube c ec preds', tc)
	else if Bf.index_of_cube c (Bf.var_index p.pred_index) = 1 then
	  Node (p.pred_index, ec, add_cube c tc preds')
	else add_cube c tree preds'
  in 
  Bf.fold_cubes (fun acc c -> add_cube c acc preds) (Leaf false) abs_obj

let cubes_to_form project_old preds abs_obj =
  let preds = List.sort (fun p p' -> compare p.pred_index p'.pred_index) 
      (if project_old then List.filter (fun p -> not (is_old p)) preds
      else preds)
  in  
  let rec convert_tree = function 
    | Leaf b -> Const (BoolConst b)
    | Node (i, ec, tc) ->
	let p = get_pred_decl i in
	smk_or [smk_and [pred_to_form false p; convert_tree tc];
		smk_and [smk_not (pred_to_form false p); convert_tree ec]]
  in 
  let tree = bf_tree_of_abs_obj preds abs_obj in
  convert_tree tree
    
let cubes_to_setexp preds abs_obj =
  let rec convert_tree = function 
    | Leaf b -> if b then Const UniversalSetConst else Const EmptysetConst
    | Node (i, ec, tc) ->
	let p = get_pred_decl i in
	let p_def = 
	  if is_singleton p then 
	    match p.pred_def with
	    | Binder (Comprehension, _, App (Const Eq, [t; _])) ->
		App (Const FiniteSetConst, [t])
	    | _ (* should never occur *) -> mk_var p.pred_name 
	  else mk_var p.pred_name
	in
	let p_def_compl = App (Const Diff, [Const UniversalSetConst; p_def]) in
	smk_cup [smk_cap [p_def; convert_tree tc];
		 smk_cap [p_def_compl; convert_tree ec]]
  in
  let tree = bf_tree_of_abs_obj preds abs_obj in
  convert_tree tree

let gamma_objs = 
  (* let hash_cons_map = Hashtbl.create 1023 in *)
  fun project_old preds abs_obj0 ->
    let abs_obj = restrict_preds project_old preds abs_obj0 in
    (* let pred_indeces = List.sort compare (List.map (fun p -> p.pred_index) preds) in
    let dnf = Bf.dnf abs_obj in 
    try Hashtbl.find hash_cons_map (project_old, pred_indeces, dnf) 
    with Not_found -> *)
      let concr_objs = cubes_to_form project_old preds abs_obj in
      (* Hashtbl.add hash_cons_map (project_old, pred_indeces, dnf) concr_objs; *)
      concr_objs

let gamma_state_dnf project_old preds abs_state =
  let max_arity = List.fold_left (fun m p -> max p.pred_arity m) 0 preds in
  smk_foralls (typed_free_var_list max_arity, gamma_objs project_old preds abs_state)


let gamma_state project_old preds abs_state0 =
  let abs_state = restrict_preds project_old preds abs_state0 in
  gamma_state_dnf project_old preds abs_state
  
let gamma_not_state project_old preds abs_state =
  let max_arity = List.fold_left (fun m p -> max p.pred_arity m) 0 preds in
  smk_foralls (typed_free_var_list max_arity, smk_not (gamma_objs project_old preds abs_state))

let gamma project_old preds abs_states =
  let process acc abs_state = gamma_state project_old preds abs_state::acc in
  smk_or (Bf_set.fold process [] abs_states)


let concretize_old_invariant preds abs_inv =
  List.fold_left (fun old_invs p ->
    if is_old p && not (is_singleton p) then 
      let p_var = Bf.mk_var p.pred_index in
      let get_opt_invs p p_var = 
	let p_inv, notp_inv = 
	  Bf.exists [p.pred_index] (Bf.conj abs_inv p_var), 
	  Bf.exists [p.pred_index] (Bf.conj abs_inv (Bf.neg p_var)) 
	in
	List.fold_right (fun q (p_inv, notp_inv) ->
	let p_inv_wo_q = Bf.exists [q.pred_index] p_inv in
	let notp_inv_wo_q = Bf.exists [q.pred_index] notp_inv in
	if is_state_pred q then p_inv_wo_q, notp_inv_wo_q else
	let p_inv' = 
	  if not (Bf.le (Bf.conj abs_inv p_inv_wo_q) p_var)
	  then p_inv else p_inv_wo_q
	in
	let notp_inv' = 
	  if not (Bf.le (Bf.conj abs_inv notp_inv_wo_q) (Bf.neg p_var))
	  then notp_inv else notp_inv_wo_q 
	in p_inv', notp_inv') preds (p_inv, notp_inv)
      in
      (* if (Bf.le (Bf.conj abs_inv p_inv) p_var) then *)
	let p_opt_inv, notp_opt_inv = get_opt_invs p p_var in 
        (* gamma_state false preds (Bf.disj (Bf.conj p_var p_opt_inv) (Bf.conj (Bf.neg p_var) notp_opt_inv)) :: old_invs *)
	let inv1 = 
	  if Bf.le p_opt_inv (Bf.neg notp_opt_inv) then
	    smk_eq (mk_var p.pred_name) (cubes_to_setexp preds p_opt_inv)
	  else mk_true
	in
	let inv2 =
	  let np = unold_pred p in
	  let np_var = Bf.mk_var np.pred_index in
	  let np_opt_inv, notnp_opt_inv = get_opt_invs np np_var in 
	  (* let _ = print_endline "opt old invariant:";
	    print_abs_state stdout (Bf.exists [np.pred_index] (Bf.conj np_var np_opt_inv));
	    print_newline ();
	    print_abs_state stdout (Bf.exists [np.pred_index] (Bf.conj (Bf.neg np_var) notnp_opt_inv))
	  in *)
          if Bf.le np_opt_inv (Bf.neg notnp_opt_inv) then
	    smk_eq (mk_var np.pred_name) (cubes_to_setexp preds np_opt_inv)
	  else mk_true
          (* let se = cubes_to_setexp preds (Bf.disj (Bf.conj p_var p_opt_inv) (Bf.conj (Bf.neg p_var) notp_opt_inv)) in
	     smk_eq se (Const UniversalSetConst) *)
        in
        (* let _ = 
	  print_endline ("old invariant:");
	  print_abs_state stdout p_opt_inv;
	  print_abs_state stdout notp_opt_inv;
	  PrintForm.print_form inv1;
          PrintForm.print_form inv2;
	in *)
	inv1 :: inv2 :: old_invs
    (* else old_invs *)
    else old_invs) [] preds 

let concretize_state_invariant preds abs_inv = 
  let null_inv =
    let null_cube = Bf.exists [null_pred] (Bf.upper_cube (Bf.conj abs_inv (Bf.mk_var null_pred))) in
    subst [(free_var_name 0, mk_null)] (gamma_objs false preds null_cube)	
  in
  let state_pred_inv =
    let invs =  List.fold_left (fun acc p ->
      let pv = Bf.mk_var (p.pred_index) in
      let p_inv =
	if Bf.le abs_inv pv then gamma_state false [p] pv
	else if Bf.le abs_inv (Bf.neg pv) then gamma_state false [p] (Bf.neg pv)
	else mk_true 
      in p_inv::acc) [] preds
    in smk_and invs
  in 
  smk_and (state_pred_inv::null_inv::get_pred_defs preds)

let concretize_invariant preds abs_inv =
  let state_inv = concretize_state_invariant preds abs_inv in
  let full_inv = gamma_state false preds abs_inv in 
  smk_and [state_inv;full_inv]
	
let cone_of_influence f =
  let fs, g = sequent_of_form f in
  let rec collect vs =
    let vs' = List.fold_left 
	(fun vs f ->
	  let fv_f = fv f in
	  if List.exists (fun v -> List.mem v vs) fv_f || List.length fv_f = 1 then
	    Util.union fv_f vs
	  else vs) vs fs
    in if Util.difference vs' vs = [] then vs else collect vs'
  in 
  let fv_g = fv g in
  if fv_g = [] then fv f else collect fv_g


(* heuristic that checks whether a predicate [p] is relevant 
 * for the abstraction of a formula [f] *)
let is_relevant f =
  let cone = cone_of_influence f in
  fun p ->
    not !BohneOptions.opt_fast_abstraction || not (is_old p) &&
    let fv_p = List.map fst p.pred_env in
    cone = [] || fv_p = [] || 
    List.exists (fun v -> List.mem v fv_p) cone

let is_relevant4ec f0 =
  let filter ty env = 
    Util.filter_map (fun (_, ty') -> ty' = ty) fst env
  in
  let f = concretize_preds f0 in
  let env = get_annotated_types f in
  let free_obj_vars_f = filter mk_object_type env in
  let _, f_succident = sequent_of_form f in
  let free_objset_vars_f = filter mk_obj_set_type (get_annotated_types f_succident) in
  fun p ->
    not (is_old p) && 
    let free_obj_vars_p = filter mk_object_type p.pred_env in
    let free_objset_vars_p = filter (mk_set_type mk_object_type) p.pred_env in
    (free_obj_vars_f = [] || free_obj_vars_p = []) &&
    (free_objset_vars_p = [] ||  
    List.exists (fun v -> List.mem v free_objset_vars_p) free_objset_vars_f) ||
    List.exists (fun v -> List.mem v free_obj_vars_p) free_obj_vars_f

let project_irrelevant preds f bf =
  let irrel_preds = List.fold_left 
      (fun acc p -> if is_relevant f p then acc else 
      p.pred_index::acc) [] preds
  in Bf.exists irrel_preds bf

let build_cubes preds exclude max_length =
  let rec extend_cubes preds complete_cubes acc =
    match preds with
    | p::preds' ->
	if exclude Bf.top true p && exclude Bf.top false p then 
	  extend_cubes preds' complete_cubes acc
	else
	  let i = p.pred_index in
	  let new_acc, curr_length =
	    List.fold_right (fun cs (acc', curr_length) ->
	      let cs' = List.fold_left
		  (fun cs c -> 
		    if exclude c false p then 
		      if exclude c true p then cs 
		      else Bf.conj (Bf.mk_var i) c::cs
		    else
		      if exclude c true p then
			Bf.conj (Bf.neg (Bf.mk_var i)) c::cs
		      else 
			Bf.conj (Bf.mk_var i) c::
			Bf.conj (Bf.neg (Bf.mk_var i)) c::cs)
		  [] cs
	      in (cs' :: acc', curr_length + 1)) acc ([[]], 0)
	  in
	  let acc', complete_cubes' =
	  if curr_length = max_length then
	    List.map2 (fun cs1 cs2 -> List.rev_append cs1 cs2) (List.tl new_acc) acc,
	    List.rev_append (List.hd new_acc) complete_cubes
	  else
	    List.map2 (fun cs1 cs2 -> List.rev_append cs1 cs2) new_acc ([]::acc),
	    complete_cubes
	  in
	  extend_cubes preds' complete_cubes' acc'
    | _ -> complete_cubes
  in
  if max_length = 0 then [] else 
  extend_cubes preds [] [[Bf.top]] 
  
let build_cubes preds exclude = Util.measure (build_cubes preds exclude)

let conj s p c = 
  Bf.conj c (if s then Bf.mk_var p.pred_index
  else Bf.neg (Bf.mk_var p.pred_index))

let disj s p c = 
  Bf.disj c (if s then Bf.mk_var p.pred_index
  else Bf.neg (Bf.mk_var p.pred_index))
 
let build_exclude_map preds max_length context_fun f notf =
  let exclude_map = Hashtbl.create 0 in
  let context = context_fun f in
  let check_pred ((f_cs, ge_f, notf_cs, ge_notf) as res) p =
    let i = p.pred_index in
    if not (is_old p) && is_relevant f p then
      let p_def = pred_to_form true p in
      let add sp sf =
	Hashtbl.add exclude_map i true;
	if sf then (disj sp p f_cs, ge_f, notf_cs, conj (not sp) p ge_notf) 
	else (f_cs, conj (not sp) p ge_f, disj sp p notf_cs, ge_notf)
      in	  
      let check sp sf cont () =
	let lhs = if sp then p_def else smk_not p_def in
	let rhs = if sf then f else notf in
	let context = context_fun (if is_singleton p then rhs else (smk_impl (lhs, rhs))) in
	if entails_fast context lhs rhs then add sp sf else cont ()
      in
      if !BohneOptions.opt_fast_abstraction && Bf.le (fst context) (Bf.mk_var i) then 
	check true true (check true false (fun () -> Hashtbl.add exclude_map i true; res)) ()
      else if !BohneOptions.opt_fast_abstraction && Bf.le (fst context) (Bf.neg (Bf.mk_var i)) then 
	check false true (check false false (fun () -> Hashtbl.add exclude_map i true; res)) ()
      else if !BohneOptions.opt_fast_abstraction && is_singleton p then
	check true true (check true false (fun () -> (*Hashtbl.add exclude_map i true;*) res)) ()
      else 
	check true true
	   (check true false
	     (check false false 
		(check false true (fun () -> res)))) ()
    else begin
      Hashtbl.add exclude_map i true; 
      res
    end
  in 
  let f_cubes, ge_f, notf_cubes, ge_notf = 
    let add_all () = List.iter (fun p -> Hashtbl.add exclude_map p.pred_index true) preds in
    let f_asms, f_cons = sequent_of_form f in
    let notf_asms, notf_cons = sequent_of_form notf in
    if entails_fast context (smk_and (f_cons :: f_asms)) mk_false then begin
      add_all ();
      (Bf.bottom, Bf.bottom, Bf.top, Bf.top)
    end 
    else if entails_fast context (smk_and (notf_cons :: notf_asms)) mk_false then begin
      add_all ();
      (Bf.top, Bf.top, Bf.bottom, Bf.bottom)
    end else
      let f_cubes, ge_f, notf_cubes, ge_notf = List.fold_left check_pred (Bf.bottom, Bf.top, Bf.bottom, Bf.top) preds in
      (* check whether over-approximations are precise *)
      if not (Bf.eq ge_f Bf.top) &&
	entails_fast context (gamma_objs true preds ge_f) f 
      then (Bf.disj f_cubes ge_f, Bf.top, notf_cubes, ge_notf)
      else if not (Bf.eq ge_notf Bf.top) &&
	entails_fast context (gamma_objs true preds ge_notf) notf
      then (f_cubes, ge_f, Bf.disj notf_cubes ge_notf, Bf.top) 
      else (f_cubes, ge_f, notf_cubes, ge_notf)
  in
  let max_length = 
    min max_length (List.length preds - Hashtbl.length exclude_map) 
  in 
  (exclude_map, ge_f, f_cubes, ge_notf, notf_cubes, max_length)
	
let abstract_expression env default e = 
  let get_pred e =
    let ty = TypeReconstruct.get_type env e in
    let p_def = match ty with
    | TypeApp (TypeBool, []) -> e
    | TypeApp (TypeObject, []) ->
	let v, ty = typed_free_var 0 in
	Binder (Comprehension, [(v, ty)], mk_eq (e, mk_var v))
    | TypeApp (TypeSet, [TypeApp (TypeObject, [])]) ->
	let v, ty = typed_free_var 0 in
	Binder (Comprehension, [(v, ty)], mk_elem (mk_var v, e))  
    | _  -> raise Not_found
    in add_pred p_def []
  in
  let rec abstract_expression e =
    match e with
    | Const NullConst -> 
	let bf_null = Bf.mk_var null_pred in
	bf_null, Bf.neg bf_null
    | Const UniversalSetConst ->
	Bf.top, Bf.bottom
    | Const EmptysetConst ->
	Bf.bottom, Bf.top
    | Const BoolConst f ->
	if f then Bf.top, Bf.bottom else Bf.bottom, Bf.top
    | App (Const Subset, [e1; e2])
    | App (TypedForm(Const Subset, _), [e1; e2])
    | App (Const Subseteq, [e1; e2]) 
    | App (TypedForm(Const Subseteq, _), [e1; e2]) ->
	let abs_e1, abs_not_e1 = abstract_expression e1 in
	let abs_e2, abs_not_e2 = abstract_expression e2 in
	Bf.disj abs_not_e1 abs_e2, 
	Bf.conj abs_e1 abs_not_e2
    | App (Const Eq, [e1; e2]) 
    | App (TypedForm(Const Eq, _), [e1; e2]) ->
	let abs_e1, abs_not_e1 = abstract_expression e1 in
	let abs_e2, abs_not_e2 = abstract_expression e2 in
	Bf.conj 
	  (Bf.disj abs_not_e1 abs_e1) 
	  (Bf.disj abs_not_e2 abs_e1),
	Bf.disj
	  (Bf.conj abs_e1 abs_not_e2)
	  (Bf.conj abs_e2 abs_not_e1)
    | App (Const Cap, es)
    | App (TypedForm(Const Cap, _), es) ->
	List.fold_left (fun (abs_es, abs_not_es) e ->
	  let abs_e, abs_not_e = abstract_expression e in
	  Bf.conj abs_es abs_e, Bf.disj abs_not_es abs_not_e)
	  (Bf.top, Bf.bottom) es
    | App (Const FiniteSetConst, es)
    | App (Const Cup, es)
    | App (TypedForm(Const Cup, _), es) ->
	List.fold_left (fun (abs_es, abs_not_es) e ->
	  let abs_e, abs_not_e = abstract_expression e in
	  Bf.disj abs_es abs_e, Bf.conj abs_not_es abs_not_e)
	  (Bf.bottom, Bf.top) es
    | App (Const Diff, [e1; e2])
    | App (TypedForm(Const Diff, _), [e1; e2]) ->
	let abs_e1, abs_not_e1 = abstract_expression e1 in
	let abs_e2, abs_not_e2 = abstract_expression e2 in
	Bf.conj abs_e1 abs_not_e2,
	Bf.disj abs_not_e1 abs_e2
    | TypedForm (e, _) -> 
	abstract_expression e 
    | _ -> 
	(try
	  let p_v = get_pred e in
	  let bf_v = Bf.mk_var p_v.pred_index in
	  bf_v, Bf.neg bf_v
	with Not_found -> default, default)
  in abstract_expression e


let fast_uabstract_form preds context inv wp_p0 =
  let wp_p1, env = TypeReconstruct.reconstruct_types [] wp_p0 in
  let abstract_expression = abstract_expression env Bf.bottom in
  let wp_p = TypeReconstruct.disambiguate wp_p1 in
  let extract_update = function
    | App (Const Eq, [e; TypedForm (Var v, _)]) 
    | App (Const Eq, [e; Var v]) 
    | App (Const Elem, [TypedForm (Var v, _); e]) 
    | App (Const Elem, [Var v; e])
      when v = free_var_name 0 -> e
    | e -> failwith ("BohneAbstraction.fast_uabstract_form: unknown update:\n"
		       ^ PrintForm.string_of_form e)
  in
  let assumes, upd_p = sequent_of_form wp_p in
  let update_expr = extract_update upd_p in
  let abstract_assume abs_upd abs_not_upd = 
    let rec abstr = function
    | App (Const Elem, [e1; e2])
    | App (Const Subseteq, [e1; e2])
    | App (Const Subset, [e1; e2]) ->
	let abs_e1, abs_not_e1 = abstract_expression e1 in
 	let abs_e2, abs_not_e2 = abstract_expression e2 in
	let abs = 
	  if Bf.eq abs_e2 (Bf.neg abs_not_e2) &&
	    Bf.le abs_e2 abs_upd
	  then abs_e1 else Bf.bottom 
	in
	let abs_not =
	  if Bf.eq abs_e1 (Bf.neg abs_not_e1) &&
	    Bf.le abs_not_e1 abs_not_upd 
	  then abs_not_e2 else Bf.bottom
	in abs, abs_not
    | App (Const Seteq, [TypedForm (App (Const Cap, t :: ts), ty); TypedForm(Const EmptysetConst, _)])
    | App (Const Seteq, [TypedForm (Const EmptysetConst, ty);  TypedForm(App (Const Cap, t :: ts), _)]) ->
	abstr (App (Const Seteq, [TypedForm (App (Const Cap, ts), ty); TypedForm (App(Const Diff, [Const UniversalSetConst; t]), ty)]))
    | App (Const Eq, [e1; e2])
    | App (Const Seteq, [e1; e2]) ->
	let abs_e1, abs_not_e1 = abstract_expression e1 in
 	let abs_e2, abs_not_e2 = abstract_expression e2 in
	let abs_1 = 
	  if Bf.eq abs_e2 (Bf.neg abs_not_e2) &&
	    Bf.le abs_e2 abs_upd 
	  then abs_e1 else Bf.bottom 
	in
	let abs_2 = 
	  if Bf.eq abs_e1 (Bf.neg abs_not_e1) &&
	    Bf.le abs_e1 abs_upd
	  then abs_e2 else Bf.bottom
	in
	let abs_not_1 =
	  if Bf.eq abs_e1 (Bf.neg abs_not_e1) then
	    if Bf.le abs_not_e1 abs_not_upd 
	    then abs_not_e2 else
	      if Bf.le abs_e1 abs_upd 
	      then abs_e2 else Bf.bottom
	  else Bf.bottom
	in
	let abs_not_2 =
	  if Bf.eq abs_e2 (Bf.neg abs_not_e2) then
	    if Bf.le abs_not_e2 abs_not_upd 
	    then abs_not_e1 else 
	      if Bf.le abs_e2 abs_not_upd 
	      then abs_e1 else Bf.bottom
	  else Bf.bottom
	in
	Bf.disj abs_1 abs_2, 
	Bf.disj abs_not_1 abs_not_2
    | App (Const Not, [App (Const Elem, [e1; e2])]) ->
	let abs_e1, abs_not_e1 = abstract_expression e1 in
 	let abs_e2, abs_not_e2 = abstract_expression e2 in
	let abs = 
	  if Bf.eq abs_e2 (Bf.neg abs_not_e2) &&
	    Bf.le abs_not_e2 abs_upd
	  then abs_e1 else Bf.bottom 
	in
	let abs_not =
	  if Bf.eq abs_e1 (Bf.neg abs_not_e1) &&
	    Bf.le abs_not_e1 abs_not_upd 
	  then abs_e2 else Bf.bottom
	in abs, abs_not
    | App (Const Not, [App (Const Eq, [TypedForm (_, TypeApp (TypeObject, [])) as e1; e2])])
    | App (Const Not, [App (Const Seteq, [TypedForm (_, TypeApp (TypeObject, [])) as e1; e2])]) ->
	let abs_e1, abs_not_e1 = abstract_expression e1 in
 	let abs_e2, abs_not_e2 = abstract_expression e2 in
	let abs_1 = 
	  if Bf.eq abs_e2 (Bf.neg abs_not_e2) &&
	    Bf.le abs_not_e2 abs_upd
	  then abs_e1 else Bf.bottom 
	in
	let abs_not_1 =
	  if Bf.eq abs_e1 (Bf.neg abs_not_e1) &&
	    Bf.le abs_not_e1 abs_not_upd 
	  then abs_e2 else Bf.bottom
	in
	let abs_2 = 
	  if Bf.eq abs_e1 (Bf.neg abs_not_e1) &&
	    Bf.le abs_not_e1 abs_upd
	  then abs_e2 else Bf.bottom 
	in
	let abs_not_2 =
	  if Bf.eq abs_e2 (Bf.neg abs_not_e2) &&
	    Bf.le abs_not_e2 abs_not_upd 
	  then abs_e1 else Bf.bottom
	in Bf.disj abs_1 abs_2, Bf.disj abs_not_1 abs_not_2

    | Binder (Forall, [(v1, _)], App (Const Not, [App (Const Elem, [TypedForm (Var v2, _); e])])) 
      when v1 = v2 ->
	let abs_e, _ = abstract_expression e in
	Bf.bottom,
	if Bf.le abs_e abs_upd then Bf.top
	else Bf.bottom
    | Binder (Forall, [(v1, ty1)], App (Const Impl, [f1_0; f2_0])) ->
	(match update_expr with
	| TypedForm (App (Const FieldRead, [_; TypedForm (Var v2, _)]), _)
	| App (Const FieldRead, [_; Var v2])
	| TypedForm (App (Const FieldRead, [_; Var v2]), _)
	| TypedForm (App (_, [TypedForm (Var v2, _)]), _)
	| App (_, [Var v2]) 
	| TypedForm (App (_, [Var v2]), _)
	  when equal_types ty1 (List.assoc v2 env) ->
	    let f1 = subst [v1, mk_var v2] f1_0
	    and f2 = subst [v1, mk_var v2] f2_0 in
	    if entails_fast context inv f1 then abstr f2
	    else Bf.bottom, Bf.bottom
	| _ -> Bf.bottom, Bf.bottom)
   (* | App (Const Or,  fs) ->
	List.fold_left (fun (abs_fs, abs_not_fs) f ->
	  let abs_f, abs_not_f = abstr f in
	  Bf.disj abs_f abs_fs, Bf.conj abs_not_f abs_not_fs)
	  (Bf.bottom, Bf.top) fs
    | App (Const And,  fs) ->
	List.fold_left (fun (abs_fs, abs_not_fs) f ->
	  let abs_f, abs_not_f = abstr f in
	  Bf.conj abs_f abs_fs, Bf.disj abs_not_f abs_not_fs)
	  (Bf.top, Bf.bottom) fs *)
    | f -> 
	try
	  match form_to_preds [] f with
	  | [p1], p2 -> 
	      let abs_e1 = Bf.mk_var p1.pred_index in
	      let abs_e2 = Bf.mk_var p2.pred_index in
	      let abs_not_e1 = Bf.neg abs_e1 in
	      let abs_not_e2 = Bf.neg abs_e2 in
	      let abs_f = 
		if Bf.eq abs_e2 (Bf.neg abs_not_e2) &&
		  Bf.le abs_e2 abs_upd
		then abs_e1 else Bf.bottom 
	      in
	      let abs_not_f =
		if Bf.eq abs_e1 (Bf.neg abs_not_e1) &&
		  Bf.le abs_not_e1 abs_not_upd 
		then abs_not_e2 else Bf.bottom
	      in abs_f, abs_not_f
	  | _ -> raise Not_found
	with Not_found -> Bf.bottom, Bf.bottom
    in abstr
  in
  let abs_upd, abs_not_upd = abstract_expression update_expr in
  let init = 
    (* if equal upd_p p.pred_def 
    then Bf.bottom, Bf.bottom
    else *) abs_upd, abs_not_upd
  in
  (* let _ = print_abs_state stdout abs_upd in *)

  let rec abstract_update (abs_wp_p, abs_wp_not_p) =
    let abs_wp_p', abs_wp_not_p' =
      List.fold_left (fun (abs_wp_p, abs_not_wp_p) f ->
	let abs_f, abs_not_f = abstract_assume (Bf.disj abs_upd abs_wp_p) (Bf.disj abs_not_upd abs_wp_not_p) f in
	if false && not (Bf.eq abs_f Bf.bottom && Bf.eq abs_not_f Bf.bottom) then begin
	  print_string "Formula: ";
	  print_string (PrintForm.string_of_form f);
	  print_endline "Current abstraction: ";
	  print_abs_state stdout abs_wp_p;
	  print_endline "---";
	  print_abs_state stdout abs_wp_not_p;
	  print_endline "Adding: ";
	  print_abs_state stdout abs_f;
	  print_endline "---";
	  print_abs_state stdout abs_not_f
	end;
	Bf.disj abs_f abs_wp_p, Bf.disj abs_not_f abs_not_wp_p) 
	(abs_wp_p, abs_wp_not_p) assumes
    in
    let has_changed = not (Bf.le abs_wp_p' abs_wp_p) || not (Bf.le abs_wp_not_p' abs_wp_not_p) in
    if has_changed then abstract_update (abs_wp_p', abs_wp_not_p')
    else abs_wp_p', abs_wp_not_p'
  in 
  let abs_wp_p, abs_wp_not_p = abstract_update init in
  forall_unknown preds abs_wp_p, forall_unknown preds abs_wp_not_p
  

let fast_alpha preds free_vars f0 =
  let pol = true in
  let f, env = TypeReconstruct.reconstruct_types [] f0 in
  let default_set = if pol then Bf_set.top else Bf_set.bottom in
  let default = if pol then Bf.top else Bf.bottom in
  let abstract_expression = abstract_expression env default in
  let is_closed_index = Bf.prime_index (Bf.var_index null_decl.pred_index) in
  let is_closed = Bf.mk_primed_var (null_decl.pred_index) in
  let mk_pair (cl_part, fr_part) =
    Bf_set.singleton (Bf.conj (Bf.impl is_closed cl_part) (Bf.impl (Bf.neg is_closed) fr_part))
  in
  let get_cl_part pair = Bf.exists_index [is_closed_index] (Bf.conj is_closed pair) in
  let get_fr_part pair = Bf.exists_index [is_closed_index] (Bf.conj (Bf.neg is_closed) pair) in
  let disj abs_fs1 abs_fs2 = 
    let res = Bf_set.fold (fun res_abs_fs pair1 ->
      let cl_part1 = get_cl_part pair1 in
      let fr_part1 = get_fr_part pair1 in
      let res = 
	Bf_set.fold (fun abs_fs pair2 ->
	  let cl_part2 = get_cl_part pair2 in
	  let fr_part2 = get_fr_part pair2 in
	  let cl_part = Bf.conj cl_part1 cl_part2 in
          let fr_part = Bf.disj fr_part1 fr_part2 in
	  Bf_set.union (mk_pair (cl_part, fr_part)) abs_fs) 
	  res_abs_fs res_abs_fs 
      in 
      Bf_set.add res pair1)
      abs_fs1 abs_fs2
    in
    res
  in
  let conj abs_fs1 abs_fs2 = 
    Bf_set.fold (fun res_abs_fs pair1 ->
      Bf_set.fold (fun res_abs_fs pair2 ->
	Bf_set.add res_abs_fs (Bf.conj pair1 pair2))
	res_abs_fs abs_fs2)
      Bf_set.bottom abs_fs1
  in
  let rec abstr f0 = 
    let abs_f, abs_not_f = match f0 with
    | App (Const Elem as c, [e1; e2])
    | App (Const Subseteq as c, [e1; e2])
    | App (Const Subset as c, [e1; e2]) when Util.disjoint (fv e1 @ fv e2) free_vars ->
	let abs_e1, abs_not_e1 = abstract_expression e1 in
 	let abs_e2, abs_not_e2 = abstract_expression e2 in
	mk_pair (Bf.disj abs_not_e1 abs_e2, Bf.top),
        (match c with 
	| Const Elem -> 
	    mk_pair (Bf.disj abs_not_e1 abs_not_e2, Bf.top)
	| _ -> default_set)
    | App (Const Eq, [e1; e2])
    | App (Const Seteq, [e1; e2]) when Util.disjoint (fv e1 @ fv e2) free_vars ->
	let abs_e1, abs_not_e1 = abstract_expression e1 in
 	let abs_e2, abs_not_e2 = abstract_expression e2 in
	mk_pair (Bf.disj (Bf.conj abs_e1 abs_e2) (Bf.conj abs_not_e1 abs_not_e2), Bf.top),
	(* Fixme: what the hack? this is only sound for equality on singletons *)
	mk_pair (Bf.disj abs_not_e1 abs_not_e2, Bf.top)
    | App (Const Not, [f]) ->
	let abs_f, abs_not_f = abstr f in
	abs_not_f, abs_f
    | App (Const Or, fs) ->
	List.fold_left (fun (abs_fs, abs_not_fs) f ->
	  let abs_f, abs_not_f = abstr f in
	  disj abs_f abs_fs, conj abs_not_f abs_not_fs)
	  (Bf_set.bottom, Bf_set.top) fs
    | App (Const And, fs) 
    | App (Const MetaAnd, fs) ->
	List.fold_left (fun (abs_fs, abs_not_fs) f ->
	  let abs_f, abs_not_f = abstr f in
	  conj abs_f abs_fs, disj abs_not_f abs_not_fs)
	  (Bf_set.top, Bf_set.bottom) fs
    | App (Const Impl, [f1; f2]) 
    | App (Const MetaImpl, [f1; f2]) ->
	let abs_f1, abs_not_f1 = abstr f1 in
	let abs_f2, abs_not_f2 = abstr f2 in
	disj abs_not_f1 (conj abs_f1 abs_f2), conj abs_f1 abs_not_f2
    | App (Const Iff, [f1 ; f2]) ->
	abstr (mk_and [mk_impl (f1, f2); mk_impl (f2, f1)])
    | App (Const Comment, [_; f]) 
    | TypedForm (f, _) -> abstr f
    | Const (BoolConst b) -> 
	if b then Bf_set.top, Bf_set.bottom
	else Bf_set.bottom, Bf_set.top
    | f -> 
	try match form_to_preds free_vars f with
	| [], p -> 
	    let abs_f = Bf.mk_var p.pred_index in
	    if Util.disjoint (fv f) free_vars then
	      mk_pair (abs_f, Bf.top), 
	      mk_pair (Bf.neg abs_f, Bf.top)
	    else
	      mk_pair (Bf.top, abs_f),
	      mk_pair (Bf.top, Bf.neg abs_f)
	| [vp], p -> 
	    let v = Bf.mk_var vp.pred_index in
	    let abs_f = Bf.disj (Bf.neg v) (Bf.conj v (Bf.mk_var p.pred_index)) in
	    let abs_not_f = Bf.disj (Bf.neg v) (Bf.conj v (Bf.neg (Bf.mk_var p.pred_index))) in
	    mk_pair (abs_f, Bf.top), mk_pair (abs_not_f, Bf.top)
	| _, p -> default_set, default_set
	with Not_found ->
	  default_set, default_set
    in
    (* print_endline "f0: "; PrintForm.print_form f0;
    print_endline "abs_f:"; print_abs_states stdout abs_f;
    print_endline "abs_not_f:"; print_abs_states stdout abs_not_f; *)
    abs_f, abs_not_f
  in
  let abs_pairs, _ = abstr f in
  let quantify = if pol then project_unknown preds else forall_unknown preds in
  let abs_f = Bf_set.map (fun pair ->
    let cl_part = get_cl_part pair in
    let fr_part = get_fr_part pair in
    quantify (Bf.conj cl_part fr_part)) abs_pairs
  in
  abs_f

let congruence_closure all_preds abs_states =
  let var_preds, preds = List.partition is_variable all_preds in
  let contains_var p v = 
    List.exists (fun (v2, _) -> v2 = v) p.pred_env
  in
  let rec cl abs_states = function 
    | [] -> abs_states
    | v1 :: var_preds ->
	let ident1, _ = get_ident v1 in
	let vbf1 = Bf.mk_var v1.pred_index in
	let abs_states' =
	  List.fold_left 
	    (fun abs_states p1 ->
	      if not (contains_var p1 ident1) then abs_states else
	      let matches = match_form preds [ident1] [] (pred_to_form true p1) in
	      List.fold_left (fun acc -> function
		| ([v2], p2) ->
		    if eq_preds v1 v2 || not (in_preds v2 all_preds) then abs_states
		    else
		      let vbf2 = Bf.mk_var v2.pred_index in		    
		      let eq_v1_v2 = Bf.equi vbf1 vbf2 in
		      let eq_p1_p2 = Bf.equi (Bf.mk_var p1.pred_index) (Bf.mk_var p2.pred_index) in
		      Bf_set.map (fun abs_state ->
			if Bf.le abs_state eq_v1_v2 then
			  Bf.conj eq_p1_p2 abs_state
			else abs_state) abs_states
		| (_, p2) -> abs_states) abs_states matches
	    ) abs_states preds
	in cl abs_states' var_preds
  in 
  let abs_states1 = cl abs_states var_preds in
  let cl2 abs_states p =
    let prefix = "$_" in
    let vs_p = free_var_list p.pred_arity in
    let vs'_p = List.map ((^) prefix) vs_p in
    let sub = List.map2 (fun x y -> (x, mk_var y)) vs_p vs'_p in
    let pdef = subst sub (pred_to_form true p) in
	
    let matched_preds = 
      List.fold_left (fun acc p' ->
	if eq_preds p p' then acc else
	let vs = free_var_list p'.pred_arity in
	let pdef' = pred_to_form true p' in
	let succ, mgu = is_unifiable [] vs pdef pdef' in
	let check_mgu = function 
	  | (true, sub_preds) ->
	      (function 
		| (v, Var v') when v' = (prefix ^ v) -> (true, sub_preds)
		| (v, t) when Util.empty (Util.intersect (fv t) vs'_p) ->
		    (try
		      let arity = free_var_index v + 1 in
		      let bvs = typed_free_var_list arity in
		      let def = Binder (Comprehension, bvs, mk_eq (t, (TypedForm (mk_var v, mk_object_type)))) in
		      let new_p = add_pred def [] in
		      (in_preds new_p all_preds, new_p :: sub_preds)
		    with Failure _ -> (false, []))
		| _ -> (false, []))
	  | _ -> function _ -> (false, [])
	in
	let succ, sub_preds = List.fold_left check_mgu (succ, []) mgu in
	if succ then (p' :: sub_preds) :: acc
	else acc) [] all_preds
    in

    let incompatible_preds = 
      List.filter (fun p' ->
	not (Util.empty (Util.difference p'.pred_dep_vars p.pred_dep_vars))) (get_all_preds ())
    in
    let projected_vars = List.map (fun p -> p.pred_index) incompatible_preds in

    List.fold_left (fun abs_states matched_ps ->
      let indices = List.map (fun p -> p.pred_index) matched_ps in
      let p_cube = List.fold_left (fun acc i -> Bf.conj (Bf.mk_var i) acc) Bf.top indices in
      Bf_set.map (fun abs_state ->
	let p_cubes = Bf.conj p_cube abs_state in
	let implied_cubes = Bf.exists (indices @ projected_vars) p_cubes in
	Bf.conj abs_state (Bf.impl (Bf.mk_var p.pred_index) implied_cubes))
	abs_states)
      abs_states matched_preds 
  in
  List.fold_left cl2 abs_states1 all_preds

let uabstract_form preds context_fun f notf skip_notf =
  let context = context_fun f in
  let _ = debug_msg 2 (fun chan ->
    output_string chan "Abstraction predicates: ";
    List.iter (fun p -> output_string chan (p.pred_name ^ " ")) preds;
    Debug.newline ();
    Printf.fprintf chan "Context:\n%s\n"
      (PrintForm.string_of_form (snd context (fst context)));
    print_abs_state stdout (fst context))
  in
  let known_nonempty = project_unknown preds (Bf.neg !empty_cubes) in
  let conj s p c = 
    Bf.conj c (if s then Bf.mk_var p.pred_index
    else Bf.neg (Bf.mk_var p.pred_index))
  in 
  let exclude_map, ge_f, f_cubes, ge_notf, notf_cubes, max_length = 
    build_exclude_map preds !max_cube_length context_fun f notf
  in
  let _ = debug_msg 2 (fun chan -> 
    output_string chan "ge_f = ";  print_cubes chan ge_f;
    output_string chan "f_cubes = "; print_cubes chan f_cubes;
    output_string chan "ge_notf = "; print_cubes chan ge_notf;
    output_string chan "notf_cubes = "; print_cubes chan notf_cubes;
    Printf.fprintf chan "max_cube_length = %d\n" max_length;
    Printf.fprintf chan "exclude_map ="; print_cubes chan
      (Hashtbl.fold (fun i _ acc -> Bf.conj (Bf.mk_var i) acc) exclude_map Bf.top))
  in
  let rec uabstract k abs_f abs_notf =
    if k > max_length then
      (Bf.conj abs_f (known_nonempty), Bf.conj abs_notf (known_nonempty))
    else
      let exclude_cubes = Bf.disj (Bf.disj !empty_cubes abs_f) abs_notf in
      let exclude c s p = 
	Hashtbl.mem exclude_map p.pred_index || 
	Bf.le (conj s p c) exclude_cubes
      in
      let cubes = build_cubes preds exclude k in
      let process_cube (abs_f, abs_notf) c = 
	let c_f = Bf.conj ge_f c in
	let def_c_f = gamma_objs true preds c_f in
	let c_notf = Bf.conj ge_notf c in
	let def_c_notf = gamma_objs true preds c_notf in
	let _ = debug_msg 4 (fun chan -> output_string chan "check f: "; print_cubes chan c_f; flush chan) in
	if (k < 2 && not (Bf.le (Bf.conj c_f (fst context)) Bf.bottom) || 
	Bf.le c_f (fst context) || not !BohneOptions.opt_fast_abstraction) && entails_fast context def_c_f f then 
	  let _ = debug_msg 4 (fun chan -> output_string chan "positive\n";) in
	  (Bf.disj c_f abs_f, abs_notf)
	else if not skip_notf && (k < 2 && not (Bf.le (Bf.conj c_notf (fst context)) Bf.bottom) || 
	Bf.le c_notf (fst context) || not !BohneOptions.opt_fast_abstraction) then
	  let _ = debug_msg 4 (fun chan -> output_string chan "check not f: "; print_cubes chan c_notf; flush chan) in
	  if entails_fast context def_c_notf notf then 
	    let _ = debug_msg 4 (fun chan -> output_string chan "positive\n") in
	    (abs_f, Bf.disj c_notf abs_notf)
	  else (abs_f, abs_notf)
	else (abs_f, abs_notf)
      in
      let abs_f', abs_notf' = List.fold_left process_cube (abs_f, abs_notf) cubes in
      uabstract (k + 1) abs_f' abs_notf'
  in
  let abs_f, abs_notf = uabstract (min 2 max_length) f_cubes notf_cubes in
  (abs_f, abs_notf)

open CachedDecider

let split_total_dp_calls = ref 0
let split_cached_dp_calls = ref 0
let split_dp_time = ref 0.0
let coerce_total_dp_calls = ref 0
let coerce_cached_dp_calls = ref 0
let coerce_dp_time = ref 0.0
	
let stack_context preds abs_state =
  if not !BohneOptions.opt_use_instantiation then gamma_state true (get_all_preds ()) abs_state else
  let stack_info = List.fold_left 
      (fun acc p -> 
	let pv = Bf.mk_var p.pred_index in
	try 
	  let var = 
	    let var_name, _ = Util.find_map 
		(function IsSingleton x -> x | _ -> None) 
		p.pred_props
	    in 
	    (* if p = null_decl then mk_null else *)
	    mk_var var_name
	  in
	  let var_cubes = Bf.conj abs_state pv in
	  let concr_var_cubes = gamma_objs true preds ((* Bf.upper_cube *) var_cubes) in
	  subst [(free_var_name 0, var)] concr_var_cubes :: acc
	with Not_found -> acc) [] preds
  in 
  smk_and (stack_info)

let fast_prune preds absstates =
  let singletons = List.filter is_singleton preds in
  Bf_set.filter 
    (fun abs_state -> 
      List.for_all 
	(fun p -> 
	  let v = Bf.mk_var p.pred_index in
	  not (Bf.le abs_state (Bf.neg v))
	) singletons
    ) absstates


let prune_empty preds context guard absstates =
  let non_empty absstate =
    let gamma_absstate = 
      gamma_state false preds absstate
    in
    let unsat = 
      measured_entails_fast split_total_dp_calls split_cached_dp_calls split_dp_time
	context guard (smk_not gamma_absstate)
    in not unsat
  in Bf_set.filter non_empty absstates

let coerce more_precise split_preds preds context guard absstates =
  let vars = List.fold_left 
      (fun acc p -> 
	if is_singleton p then
	  Bf.disj (Bf.mk_var p.pred_index) acc
	else acc)
      Bf.bottom preds
  in
  let split_preds = if more_precise then preds else split_preds in
  let check_cube absstate acc c =
    let context absstate = 
      (absstate, 
       if true || not more_precise then stack_context preds 
       else fun absstate -> 
	 smk_and [stack_context preds absstate; 
		  gamma_state true (*split_*)preds absstate]) 
    in
    (* check whether a cube is empty and if so, remove it from the processed abstract state *)
    let check_cube acc c =
      let is_empty = 
	measured_entails_fast coerce_total_dp_calls coerce_cached_dp_calls coerce_dp_time
	  (context absstate) guard (gamma_not_state true preds c) 
      in
      if is_empty then Bf.conj acc (Bf.neg c) else acc
    in
    (* split cube into its subsumed cubes and check them for nonemptiness *)
    let rec split_and_check num_of_splits acc cube continue = function 
      |	[] -> (* let acc' = check_cube acc cube in *) continue acc
      |	p :: preds -> 
	  let cube_and_p = conj true p cube in
	  let cube_and_notp = conj false p cube in
	  if num_of_splits > 0 && preds <> [] then 
	    split_and_check (num_of_splits - 1) acc cube_and_p 
	      (fun acc -> 
		split_and_check (num_of_splits - 1) acc cube_and_notp continue preds)
	      preds
	  else
	    let acc1 = check_cube acc cube_and_p in 
	    let acc2 = check_cube acc1 cube_and_notp in
	    split_and_check 0 acc2 cube continue preds
    in
    let make_cubes = List.fold_left 
	(fun (base_cube, length, num_preds, nondet_preds) q -> 
	  let qi = q.pred_index in
	  if Bf.index_of_cube c (Bf.var_index qi) = 1 then
	    (conj true q base_cube, length + 1, num_preds + 1, nondet_preds)
	  else if Bf.index_of_cube c (Bf.var_index qi) = 0 then 
	    (conj false q base_cube, length + 1, num_preds + 1, nondet_preds)
	  else if Bf.index_of_cube c (Bf.var_index qi) = 2 && is_relevant guard q && in_preds q split_preds
	  then (base_cube, length, num_preds + 1, q :: nondet_preds)
	  else (base_cube, length + 1, num_preds + 1, nondet_preds))
	(Bf.top, 0, 0, [])
    in
    let base_cube, base_cube_length, num_preds, nondet_preds = make_cubes preds in 
    (* do not check non-emptiness of complete singleton cubes *)
    if false && more_precise || not (base_cube_length = num_preds && Bf.le base_cube vars )
    then split_and_check 2 acc base_cube (fun acc -> acc) nondet_preds 
    else acc
  in
  let pruned = prune_empty preds context guard absstates in
  Bf_set.map (fun absstate ->
    let non_var_cubes = if more_precise then absstate else Bf.conj (Bf.neg vars) absstate in
    Bf.fold_cubes (check_cube absstate) absstate non_var_cubes) pruned


let alpha preds context invariants f0 =
  let f = mk_impl (invariants, f0) in
  let notf = mk_impl (invariants, smk_not f0) in
  let known_nonempty = project_unknown preds (Bf.neg !empty_cubes) in
  let abs_notf, _ = uabstract_form preds (fun _ -> context) notf f true in
  let abs_f = project_unknown preds (Bf.conj (Bf.neg abs_notf) known_nonempty) in
  abs_f 
    

let split_equalities preds absstates =
  let rec split eqs acc =
    function
    | [] -> acc
    | p::preds ->
	(* assert (is_singleton p); *)
	let v1 = Bf.mk_var p.pred_index in
	let acc_eq = List.fold_left (fun acc_eq p' ->
	  let v2 = Bf.mk_var p'.pred_index in
	  Bf_set.union acc_eq (Bf_set.conj acc (Bf.equi v1 v2))) Bf_set.bottom eqs 
	in
	let acc_neq = 
	  let neqs = List.fold_left (fun acc_neq p' -> 
	    let v2 = Bf.mk_var p'.pred_index in
	    Bf.conj acc_neq (Bf.neg (Bf.conj v1 v2))) Bf.top eqs
	  in Bf_set.conj acc neqs
	in
	Bf_set.union (split (p::eqs) acc_neq preds) (split eqs acc_eq preds)
  in
  match preds with
  | [] -> absstates
  | p::preds1 -> 
      let split_abs_states = split [p] absstates preds1 in
      fast_prune preds split_abs_states
		       


let split_state_preds preds absstates =
  let split acc p =
    let pv = Bf.mk_var p.pred_index in
    Bf_set.fold (fun acc absstate ->
      Bf_set.add (Bf_set.add acc (Bf.conj absstate pv)) 
	(Bf.conj absstate (Bf.neg pv))) Bf_set.bottom acc
  in List.fold_left split absstates preds

let split preds absstates = 
  let singleton_preds = List.filter is_singleton preds in
  let state_preds = List.filter is_state_pred preds in
  split_state_preds state_preds (split_equalities singleton_preds absstates)
      

let split_singletons preds split_preds absstates =
  (* let known_nonempty = project_unknown preds (Bf.neg !empty_cubes) in *)
  let process p acc absstate =
    let res = ref acc in
    let p_cubes = Bf.conj absstate (Bf.mk_var p.pred_index) in
    let notp_cubes = Bf.conj absstate (Bf.neg (Bf.mk_var p.pred_index)) in
    let process_cube c =
      let p_cubes = List.fold_left
	  (fun p_cubes q ->
	    let qi = q.pred_index in
	    if Bf.index_of_cube c (Bf.var_index qi) = 1 then
	      List.rev_map (Bf.conj (Bf.mk_var qi)) p_cubes
	    else if Bf.index_of_cube c (Bf.var_index qi) = 0 then 
	      List.rev_map (Bf.conj (Bf.neg (Bf.mk_var qi))) p_cubes
	    else if (is_relevant (p.pred_def) q) && not (is_state_pred q) 
	    then List.fold_left 
		(fun acc c -> 
		  let c_and_q = Bf.conj (Bf.mk_var qi) c 
		  and c_and_notq = Bf.conj (Bf.neg (Bf.mk_var qi)) c in
		  if not (Bf.le c_and_q !empty_cubes) then 
		    if not (Bf.le c_and_notq !empty_cubes) then
		      c_and_q::c_and_notq::acc
		    else c_and_q::acc
		  else c_and_notq::acc) [] p_cubes
	    else p_cubes
	  ) [Bf.top] preds in
      List.iter (fun c -> 
	let absstate' = Bf.disj notp_cubes c in
	res := Bf_set.add !res absstate') p_cubes
    in
    let _ = Bf.foreach_cube p_cubes process_cube in
    !res
  in
  let process_p acc p =
    Bf_set.fold (process p) Bf_set.bottom acc
  in
  List.fold_left process_p absstates split_preds
  
