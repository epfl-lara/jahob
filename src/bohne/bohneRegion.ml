open Bf
open Bf_set
open Ast
open AstUtil
open Util
open Form
open FormUtil
open BohnePred
open BohneUtil
open BohneProgram
open BohneAbstraction
 
(** Cubes of Predicates *)
type cube = Bf.t

(** Abstract states *)
type abs_state = Bf.t

(** Sets of abstract states *)
type abs_states = Bf_set.bf_set

(** Region *)
type region = {
    ppoint : program_point;
    timestamp : int;
    mutable invariant : form list;
    mutable absinvariant : abs_states;
    mutable preds : pred_decl list;
    mutable split_preds : pred_decl list;
    mutable inherited_preds : pred_decl list;
    mutable absstates : abs_states;
    mutable parent : (guarded_command * abs_states * region ref);
    mutable succs : (guarded_command * region) list;
    mutable subsumed : bool;
  }

let timecount = ref 0 

(** Create the root region *)
let mk_root_region entry_point init_pred_decls invariant init = 
  timecount := 0;
  let parent_gc = {gc_havoc = []; gc_guard = init; gc_command = []} in
  let rec root = 
    {ppoint = entry_point;
     timestamp = !timecount;
     invariant = init :: invariant;
     absinvariant = Bf_set.top;
     preds = init_pred_decls;
     split_preds = [];
     inherited_preds = [];
     absstates = Bf_set.bottom;
     parent = (parent_gc, Bf_set.top, ref root);
     succs = [];
     subsumed = false;
   }
  in root

let is_root region = 
  let _, _, parent_ref = region.parent in
  !parent_ref == region

let region_equal r1 r2 = r1 == r2


(** Create a successor region *)
let mk_succ parent command succ_pp succ_preds succ_split_preds src_states succ_invs =
  timecount := !timecount + 1;
  let inherited = 
    (*union_preds 
      (List.filter inherits parent.preds)*)
      parent.inherited_preds 
  in
  let succ_region =
    {ppoint = succ_pp;
     timestamp = !timecount;
     invariant = succ_invs;
     absinvariant = Bf_set.top;
     preds = union_preds (List.filter (inherits_to succ_pp) inherited) succ_preds;
     split_preds = succ_split_preds;
     inherited_preds = inherited;
     absstates = Bf_set.bottom;
     parent = (command, src_states, ref parent);
     succs = [];
     subsumed = false;
   } 
  in
  parent.succs <- (command, succ_region) :: parent.succs;
  succ_region

let get_parent_pp r =
  let _, _, parent_ref = r.parent in
  !parent_ref.ppoint

let is_parent p r =
  let _, _, parent_ref = r.parent in 
  region_equal !parent_ref p 

(** Lfp data structure. It maps a control flow point p to the
   projection of all abstract states in regions for p. *)

type lfp_node = {
    mutable lfp_preds : pred_decl list;
    mutable lfp_absstates : (form * abs_states) list
  }

type lfp = (int, lfp_node) Hashtbl.t

let get_lfp_node lfp pp_id =
  try Hashtbl.find lfp pp_id 
  with | Not_found ->
    let new_node = {lfp_preds = []; lfp_absstates = []} in
    Hashtbl.add lfp pp_id new_node;
    new_node

let find_in_lfp lfp pp_id guard =
  try 
    let lfp_node = Hashtbl.find lfp pp_id in
    List.assoc guard lfp_node.lfp_absstates
  with Not_found -> Bf_set.bottom

let project_lfp_by_guard lfp pp_id guard =
  try
    let lfp_node = Hashtbl.find lfp pp_id in
    let abs_states =
      List.fold_left (fun acc (guard', s) -> 
	if not (entails_synt guard' (smk_not guard))
	then Bf_set.union s acc else acc)
	Bf_set.bottom lfp_node.lfp_absstates
    in (abs_states, lfp_node.lfp_preds)
  with Not_found -> (Bf_set.bottom, [])
  
let project_lfp lfp pp_id =
  try
    let lfp_node = Hashtbl.find lfp pp_id in
    let abs_states =
      List.fold_left (fun acc (guard, s) -> 
	(guard, Bf_set.join s)::acc)
	[] lfp_node.lfp_absstates
    in (abs_states, lfp_node.lfp_preds)
  with Not_found -> ([(mk_true, Bf.bottom)], [])



let update_lfp_by_guard lfp pp_id guard new_abs_states =
  let lfp_node = get_lfp_node lfp pp_id in
  let abs_states, abs_state_list' = 
    try assoc_remove guard lfp_node.lfp_absstates
    with Not_found -> (Bf_set.bottom, lfp_node.lfp_absstates)
  in
  let abs_states' = Bf_set.union abs_states new_abs_states in
  lfp_node.lfp_absstates <- (guard, abs_states')::abs_state_list';
  abs_states'
   
let update_lfp lfp pp_id new_abs_states =
  update_lfp_by_guard lfp pp_id mk_true new_abs_states

let add_preds_to_lfp lfp pp_id new_preds =
  let lfp_node = get_lfp_node lfp pp_id in
  lfp_node.lfp_preds <- union_preds new_preds lfp_node.lfp_preds

let find_preds lfp pp_id =
  try (Hashtbl.find lfp pp_id).lfp_preds with Not_found -> []


let collect region pp =
  let rec collect acc r =
    let acc' = 
      if r.ppoint.pp_id = pp.pp_id then 
	let _, _, parent_ref = r.parent in
	assoc_replace !parent_ref.ppoint (fun s ->
	  Bf_set.union r.absstates s) r.absstates acc
      else acc
    in
    List.fold_left (fun acc (_, child) -> collect acc child) acc' r.succs
  in
  List.rev_map snd (collect [] region)


let collect_invariants region pp =
  let rec collect (first, acc) r =
    let first', acc' = 
      if r.ppoint.pp_id = pp.pp_id then
	if first then
	  false, r.invariant
	else 
	  false, List.filter 
	    (fun f -> List.exists (fun g -> equal f g) acc) r.invariant
      else first, acc
    in List.fold_left (fun acc (_, child) -> collect acc child) (first', acc') r.succs
  in
  snd (collect (true, []) region)

(** Remove the subtree starting in [region] from the region tree *)
let remove_subtree helper acc region =
  let rec traverse acc todo =
    match todo with
    | r::todo' ->
	r.succs <- [];
	if not (is_root r) then r.absstates <- Bf_set.bottom;
	traverse (helper acc r) (List.fold_left (fun acc (_, child) -> child::acc) todo' r.succs)
    | [] -> acc
  in traverse acc [region]

(** Recompute the lfp data structure *)
let recompute_lfp timestamp lfp root_region =
  Hashtbl.clear lfp;
  let rec traverse todo reconsider =
    match todo with
    | r::todo' ->
	let reconsider' = 
	  if r.subsumed && r.timestamp > timestamp 
	  then (r.subsumed <- false; r :: reconsider) 
	  else reconsider
	in
	let gc, src_states, parent_ref = r.parent in
	add_preds_to_lfp lfp r.ppoint.pp_id r.preds;
	if not (is_root r) then
	  ignore (update_lfp_by_guard lfp !parent_ref.ppoint.pp_id gc.gc_guard src_states);
	traverse (List.fold_left (fun acc (_, child) -> child::acc) todo' r.succs) reconsider'
    | [] -> reconsider
  in traverse [root_region] []


(** Add predicates to a region *)
let add_preds lfp region preds =
  region.preds <- union_preds preds region.preds;
  add_preds_to_lfp lfp region.ppoint.pp_id preds

let lfp_stats lfp = 
  let num_locs, num_abs_states = 
    Hashtbl.fold (fun _ lfp_node (num, card) ->
      let abs_states = List.fold_left (fun acc (_, abs_states) ->
	Bf_set.union acc abs_states) Bf_set.bottom lfp_node.lfp_absstates
      in (num + 1, card + Bf_set.card abs_states)) lfp (0, 0)
  in if num_locs <> 0 then float num_abs_states /. float num_locs else 0.


let region_tree_stats root_region =
  let rec traverse (size, longest_sibling_path, total_preds, total_local_preds, max_local_preds) region =
    let size', longest_path', total_preds', total_local_preds', max_local_preds' =
      List.fold_left (fun (size', longest_path', total_preds', total_local_preds', max_local_preds') (_, succ_region) ->
	traverse (size', longest_path', total_preds', total_local_preds', max_local_preds') succ_region)
	(size, 0, total_preds, total_local_preds, max_local_preds) region.succs
    in 
    let relevant_preds = List.filter (fun p -> not (inherits p) || inherits_to region.ppoint p) region.preds in
    size' + 1, 
    max  longest_sibling_path (longest_path' + 1),
    union_preds relevant_preds (union_preds total_preds' total_preds),
    total_local_preds' + (List.length relevant_preds),
    max max_local_preds' (List.length relevant_preds)
  in traverse (0, 0, [], 0, 0) root_region

(** Print ART starting from [root_region] in graphviz format *)
let print_region_tree chan root_region =
  let rec print region =
    let preds_str = 
      List.fold_left (fun acc p ->  acc ^ (if acc <> "" then ", " else "") ^ p.pred_name)  "" region.preds
    in
    let label_str = 
      Printf.sprintf "pp: %d\\npreds: %s" region.ppoint.pp_id preds_str
    in
    let geom_str = 
      if region.subsumed then 
	"shape=box,style=filled,color=\".7 .3 1.0\""
      else "shape=box"
    in
    Printf.fprintf chan "%d [label=\"%s\",%s];\n" region.timestamp label_str geom_str;
    List.iter (fun (_, succ_region) -> 
      Printf.fprintf chan "%d -> %d;\n" region.timestamp succ_region.timestamp;
      print succ_region) region.succs
  in 
  output_string chan "digraph ART {\n";
  print root_region;
  output_string chan "}\n"
