open Form
open FormUtil

type status =
  | KnownStatus of bool * string
  | UnknownStatus of string list 

type cache_entry = {
    orig_query : form;
    status : status;
    minimized : bool;
    mutable cache_hits : int;
  }

module type SET_QUERY_CACHE =
  sig
    type 'a query_cache
    type elem = int
    type set = elem list

    val empty_cache : 'a query_cache
	
    val insert : 'a query_cache -> set -> 'a -> 'a query_cache

    val exists_superset : 'a query_cache -> set -> bool
    val exists_subset : 'a query_cache -> set -> bool

    val print : 'a query_cache -> unit
    val print_stats : 'a query_cache -> unit
  end

module SetQueryCache : SET_QUERY_CACHE =
  struct
    type 'a query_cache =
      | Leaf of 'a option
      | Node of int * 'a query_cache * 'a query_cache

    type elem = int
    type set = elem list

    let empty_cache = Leaf None

    let trans_from_set set =
      let trans, last = 
	List.fold_left (fun (trans, last) i ->
	  if i = last + 1 then (trans, i) else
	  (i :: last + 1 :: trans, i)) 
	  ([], -1) set
      in 
      List.rev  (last + 1 :: trans)

    (* let insert root set e =
      let trans = trans_from_set set in
      let rec insert v trans = function
	| Leaf _ as n ->
	    (match trans with
	    | [] -> Leaf (Some e)
	    | t :: trans' ->
		if not v then Node (t, insert (not v) trans' (Leaf None), n)
		else Node (t, n, insert (not v) trans' (Leaf None)))
	| Node (t1, l, r) as n ->
	    (match trans with
	    | [] -> 
		if v then Node (t1, insert v trans l, r)
		else Node (t1, l, insert v trans r)
	    | t2 :: trans' ->
		if t1 = t2 then 
		  if not v then Node (t1, insert (not v) trans' l, r)
		  else Node (t2, l, insert (not v) trans' r)
		else if t2 < t1 then
		  if v then Node (t2, n, insert (not v) trans' (Leaf None))
		  else Node (t2, insert (not v) trans' (Leaf None), n)
		else 
		  if v then Node (t1, insert v trans l, r)
		  else Node (t1, l, insert v trans r))
      in insert true trans root

    let exists_superset root set = 
      let rec some_leaf = function
	|	Leaf None -> false
	|	Leaf _ -> true
	| Node (_, l, r) -> some_leaf l || some_leaf r
      in
      let trans = trans_from_set set in
      let rec search trans v w = function
	| Leaf None -> false
	| Leaf _ -> 
	    (match trans with
	    | [] -> w || not v
	    | _ -> w)
	| Node (t1, l, r) as n ->
	    match trans with 
	    | [] -> assert (not v); some_leaf n
	    | t2 :: trans' ->
		if t1 = t2 then 
		  if v then 
		    search trans' (not v) true l || 
		    search trans' (not v) false r
		  else 
		    search trans' (not v) true l
		else if t1 < t2 then
		  if v then search trans v true l
		  else search trans v true l || search trans v false r
		else 
		  if w then search trans' (not v) w n
		  else false
      in search trans true true root

    let exists_subset root set = 
      let trans = trans_from_set set in
      let rec search trans v w = function
	| Leaf None -> false
	| Leaf _  -> 
	    (match trans with
	    | [] -> not w || v
	    | _ -> not w)
	| Node (t1, l, r) as n ->
	    match trans with 
	    | [] -> assert (not v); search trans v false r
	    | t2 :: trans' ->
		if t1 = t2 then 
		  if not v then 
		    search trans' (not v) true l || 
		    search trans' (not v) false r
		  else 
		    search trans' (not v) false r
		else if t1 < t2 then
		  if not v then search trans v false r
		  else search trans v true l || search trans v false r
		else 
		  if not w then search trans' (not v) w n
		  else false
      in search trans true true root *)

    let insert root set e =
      let rec insert set = function
	| Leaf _ as n ->
	    (match set with
	    | [] -> Leaf (Some e)
	    | t :: set' ->
		Node (t, insert set' (Leaf None), n))
	| Node (t1, l, r) as n ->
	    (match set with
	    | [] -> 
		Node (t1, l, insert set r)
	    | t2 :: set' ->
		if t1 = t2 then 
		  Node (t1, insert set' l, r)
		else if t2 < t1 then
		  Node (t2, insert set' (Leaf None), n)
		else 
		  Node (t1, l, insert set r))
      in insert set root

    let exists_superset root set = 
      let rec search set = function
	| Leaf None -> false
	| Leaf _ -> set = []
	| Node (t1, l, r) ->
	    match set with 
	    | [] -> search set l || search set r
	    | t2 :: set' ->
		if t1 = t2 then 
		  search set' l
		else if t1 < t2 then
		  search set l || search set r
		else false
      in search set root

    let exists_subset root set = 
      let rec search set = function
	| Leaf None -> false
	| Leaf _  -> true
	| Node (t1, l, r) as n ->
	    match set with 
	    | [] -> search set r
	    | t2 :: set' ->
		if t1 = t2 then 
		  search set' l || search set' r
		else if t1 < t2 then
		  search set r
		else search set' n
      in search set root

    let rec print = function
      |	Leaf None -> print_string "L"
      |	Leaf _  -> print_string "R"
      |	Node (t, l, r) ->
	  Printf.printf "N (%d, " t;
	  print l;
	  print_string ", ";
	  print r;
	  print_string ")"
 
    let rec print_stats root =
      let rec stats = function
	| Leaf None -> 0, 0, 0
	| Leaf (Some e) -> 0, 0, 1
	| Node (_, l, r) ->
	    let lsize, ldepth, lentries =
	      stats l
	    in
	    let rsize, rdepth, rentries =
	      stats r
	    in
	    lsize + rsize + 1, 
	    max ldepth rdepth + 1, 
	    lentries + rentries
      in
      let size, depth, entries = stats root in
      Printf.printf "Cache size: %d\nCache depth: %d\nCache entries: %d\n"
	size depth entries

  end

(*
let _ = 
  let cache =
     SetQueryCache.insert 
      (SetQueryCache.insert 
	 (SetQueryCache.insert (SetQueryCache.empty_cache)
	    [3; 6; 8] true)
	 [3; 6] true)
      [3; 6; 8; 10] true
  in 
  SetQueryCache.print cache; 
  print_newline ();
  print_endline (string_of_bool (SetQueryCache.exists_subset cache []));
  print_endline (string_of_bool (SetQueryCache.exists_subset cache [3]));
  print_endline (string_of_bool (SetQueryCache.exists_subset cache [3; 6; 8]));
  print_endline (string_of_bool (SetQueryCache.exists_subset cache [3; 6; 4]));
  print_endline (string_of_bool (SetQueryCache.exists_subset cache [3; 6; 8; 10]));
  exit 0
*)

let valid_cache = ref (SetQueryCache.empty_cache)
let invalid_cache = ref (SetQueryCache.empty_cache)

let set_from_key =
  let item_counter = ref 0 in
  let item_map = Hashtbl.create 0 in
  fun key ->
    let fitems = match key with
    | App (Const MetaAnd, fs) -> fs
    | f -> [f]
    in
    let items = List.map (fun f ->
      try Hashtbl.find item_map f
      with Not_found -> 
	let item = !item_counter in
	Hashtbl.add item_map f item;
	incr item_counter;
	item) fitems
    in 
    List.sort compare items

let total_cache_hits = ref 0 
let valid_cache_hits = ref 0 
let invalid_cache_hits = ref 0 

let cache = Hashtbl.create 1000

let result_from_status = function
    | KnownStatus (res, prover_id) -> res, prover_id
    | UnknownStatus _ -> false, ""

let alpha_rename env (sub, cnt_map, ty_map) f =
  let var_id cnt_map ty_id =
    let cnt = 
      try List.assoc ty_id cnt_map 
      with Not_found -> 0
    in cnt + 1, (ty_id, cnt + 1) :: List.remove_assoc ty_id cnt_map 
  in
  let type_id ty_map ty =
    try List.assoc ty ty_map, ty_map 
    with Not_found ->
      let id = match ty_map with
      | [] -> 0
      | (_, last_id) :: _ -> last_id + 1
      in
      id, (ty, id) :: ty_map 
  in
  let add_sub (var, ty) (sub, cnt_map, ty_map) =
    let ty_id, ty_map' = type_id ty_map ty in
    let var_id, cnt_map' = var_id cnt_map ty_id in
    (var, Printf.sprintf "var_%d_%d" ty_id var_id) :: sub, cnt_map', ty_map'
  in
  let exclude = pseudo_constants in
  let fvs0 = List.map (fun v -> v, List.assoc v env) (Util.difference (fv f) (exclude @ List.map fst sub)) in
  let fvs = List.stable_sort (fun (_, ty1) (_, ty2) -> compare ty2 ty1) fvs0 in
  let sub, cnt_map, ty_map = 
    List.fold_right add_sub fvs (sub, cnt_map, ty_map) 
  in
  let rec rename sub cnt_map ty_map = function
    | Var v when not (List.mem v exclude) -> 
	(try
	  Var (List.assoc v sub)
	with Not_found -> print_endline v; exit 1)
    | App (f, fs) -> 
	App (rename sub cnt_map ty_map f, List.map (rename sub cnt_map ty_map) fs)
    | Binder (b, vs, f) ->
	let sub', cnt_map', ty_map' = List.fold_right add_sub vs (sub, cnt_map, ty_map) in
	Binder (b, List.map (fun (v, ty) -> List.assoc v sub', ty) vs, rename sub' cnt_map' ty_map' f)
    | TypedForm (f, ty) -> 
	TypedForm (rename sub cnt_map ty_map f, ty)
    | f -> f
  in rename sub cnt_map ty_map f, (sub, cnt_map, ty_map)

let key_from_query env sub f0 = 
  let rec simplify = function
    | App (Var rtrancl, [f; t1; t2])
      when rtrancl = str_rtrancl && equal t1 t2 
      -> mk_true  
    | App (Const Eq, [t1; t2]) 
    | App (Const GtEq, [t1; t2])
    | App (Const LtEq, [t1; t2])
    | App (Const Subseteq, [t1; t2])
    | App (Const Seteq, [t1; t2]) when equal t1 t2 -> mk_true
    | App (Const Eq, [Const (BoolConst b); f])
    | App (Const Eq, [f; Const (BoolConst b)]) ->
	if b then simplify f else smk_not (simplify f)
    | App (Const MetaAnd, fs) 
    | App (Const And, fs) -> 
	smk_and (List.map simplify fs)
    | App (Const Or, fs) -> 
	smk_or (List.map simplify fs)
    | App (Const Not, [f]) -> smk_not (simplify f)
    | App (Const Impl, [f1; f2]) 
    | App (Const MetaImpl, [f1; f2]) -> 
	smk_impl (simplify f1, simplify f2)
    | Binder (Forall, vs, f) ->
	smk_foralls (vs, simplify f)
    | Binder (Exists, vs, f) ->
	smk_exists (vs, simplify f)
    | f -> f
  in
  let asms, hyp = sequent_of_form f0 in
  let sq1 = elim_fv_in_seq false (smk_not hyp :: asms, mk_false) in
  let f1 = form_of_sequent sq1 in
  let f2 = unlambda ~keep_comprehensions:false f1 in
  let f3 = reduce f2 in
  let f4 = simplify f3 in
  let asms, hyp = sequent_of_form f4 in
  let key0 = if equal hyp mk_true then mk_false 
  else mk_metaand (List.stable_sort compare asms) in
  let key, sub = alpha_rename env sub key0 in 
  ParseForm.parse_formula (PrintForm.string_of_form key), sub

let find_query env f =
  let key, _ = key_from_query env ([], [], []) f in
  try
    let res = Hashtbl.find cache key in
    incr total_cache_hits; 
    res.cache_hits <- res.cache_hits + 1;
    res.status
  with Not_found ->
    let key_set = set_from_key key in
    if SetQueryCache.exists_subset !valid_cache key_set then
      let _ = incr valid_cache_hits in
      KnownStatus (true, "Cache")
    else if SetQueryCache.exists_superset !invalid_cache key_set then
      let _ = incr invalid_cache_hits in
      KnownStatus (false, "Cache")
    else (raise Not_found)


let insert_query env f status =
  let key, _ = key_from_query env ([], [], []) f in
  let entry = 
    { orig_query = f;
      status = status;
      minimized = false;
      cache_hits = 0
    }
  in Hashtbl.add cache key entry

let insert_minimized env f min_f status =
  let key0, sub = key_from_query env ([], [], []) f in
  let key, _ = key_from_query env sub min_f in
  (* let _ = print_endline "\nkey before minimize"; PrintForm.print_form key0 in
  let _ = print_endline "key after minimize"; PrintForm.print_form key in *)
  let entry = 
    { orig_query = f;
      status = status;
      minimized = true;
      cache_hits = 0
    }
  in Hashtbl.add cache key entry

let remove_query env f =
  let key, _ = key_from_query env ([], [], []) f in
  Hashtbl.remove cache key

let fold fn acc =
  Hashtbl.fold fn cache acc

let iter fn =
  Hashtbl.iter fn cache

let load_cache () =
  let process_entry (valid_queries, invalid_queries) e =
    try
      let query, key, status =
	Xml.fold 
	  (fun (query, key, status) c ->
	    if Xml.tag c = "query" then
	      let query_string = Xml.pcdata (List.hd (Xml.children c)) in
	      let query1 = ParseForm.parse_formula query_string in
	      query1, key, status
	    else if Xml.tag c = "key" then
	      let key_string = Xml.pcdata (List.hd (Xml.children c)) in
	      let key1 = ParseForm.parse_formula key_string in
	      query, key1, status
	    else
	      let id = Xml.attrib c "name" in
	      let res = Xml.attrib c "status" in
	      let status1 = 
		if res = "valid" then KnownStatus (true, id)
		else if res = "invalid" then KnownStatus (false, id)
		else match status with
		| UnknownStatus ids -> UnknownStatus (id :: ids)
		| _ -> status
	      in 
	      query, key, status1
	  ) (Const Unit, Const Unit, UnknownStatus []) e
      in
      let minimized = 
	try bool_of_string (Xml.attrib e "minimized")
	with Xml.No_attribute _ -> false
      in
      let hits =
	try int_of_string (Xml.attrib e "hits")
	with Xml.No_attribute _ -> 0
      in	  
      let entry = 
	{ orig_query = query;
	  status = status;
	  minimized = minimized;
	  cache_hits = hits
	}
      in
      (* Hashtbl.add cache key entry; *)
      let query_set = set_from_key key in
      let res, _ = result_from_status entry.status in
      if res then (SetQueryCache.insert valid_queries query_set entry, invalid_queries)
      else (valid_queries, SetQueryCache.insert invalid_queries query_set entry)
    with _ -> 
      Util.warn "Ignoring broken entry in persistent cache";
      valid_queries, invalid_queries
  in
  try
    let xml_cache = Xml.parse_file !CmdLine.cache_file_name in
    let valid_queries, invalid_queries = Xml.fold process_entry (!valid_cache, !invalid_cache) xml_cache in
    SetQueryCache.print_stats valid_queries;
    SetQueryCache.print_stats invalid_queries;
    valid_cache := valid_queries;
    invalid_cache := invalid_queries
  with
  | Xml.File_not_found s -> Util.warn ("Could not find persistent cache: " ^ s)
  | Xml.Error e -> Util.warn ("Could not parse persistent cache: " ^ Xml.error e)

let store_cache filter =
  let old_entries = 
    try 
      let xml_cache = Xml.parse_file !CmdLine.cache_file_name in
      Xml.children xml_cache
    with | Xml.File_not_found _ | Xml.Error _ -> []
  in
  let entries, _ = 
    Hashtbl.fold 
      (fun key entry (acc, number) ->
	if not (filter entry) then acc, number else
	  let attrib = 
	    [("number", string_of_int number);
	     ("minimized", string_of_bool entry.minimized); 
	     ("hits", string_of_int entry.cache_hits)]
	  in
	  let xml_key =
	    Xml.Element ("key", [], [Xml.PCData (PrintForm.string_of_form key)])
	  in
	  let xml_query =
	    Xml.Element ("query", [], [Xml.PCData (PrintForm.string_of_form entry.orig_query)])
	  in
	  let xml_status =
	    match entry.status with
	    | KnownStatus (res, id) -> 
		[Xml.Element ("prover", [("name", id); ("status", if res then "valid" else "invalid")], [])]
	    | UnknownStatus ids ->
		List.map (fun id ->
		  Xml.Element ("prover", [("name", id); ("status", "unknown")], [])) ids
	  in
	  Xml.Element ("entry", attrib, xml_key :: xml_query :: xml_status) :: acc, number + 1
      ) cache (old_entries, List.length old_entries + 1)
  in 
  let xml_cache = Xml.Element ("cache", [("lastmodified", "")], entries) in
  let cache_file = open_out !CmdLine.cache_file_name in
  output_string cache_file (Xml.to_string_fmt xml_cache);
  close_out cache_file

let alpha_rename f = fst (alpha_rename (TypeReconstruct.get_env f) ([], [], []) f)
  
