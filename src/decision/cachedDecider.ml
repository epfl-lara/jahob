open Common
open Form
open FormUtil
open Slice
open Decider
open TermRewrite
open TptpPrettyPrinter
open PersistentCache

(* debug messages *)
let debug_msg = Debug.debug_print_msg (Debug.register_debug_module "CachedDecider")

type cache_stats = {
    calls : int;
    cache_hits : int;
    total_time : float;
    total_dp_time : float;
    max_time : float;
    max_query : form;
  }

module type Lattice =
 sig 
   type t
   val eq : t -> t -> bool
   val le : t -> t -> bool
   val join : t list -> t
   val meet : t list -> t
   val top : t 
   val bottom : t
 end

module type CachedDecider = 
  sig
    type t
    
    val decide : (t * (t -> form)) -> form -> bool
    val decide_fast : (t * (t -> form)) -> form -> bool
    val register_filter : string -> (typeEnv -> sequent -> sequent) -> unit
    val stats : unit -> cache_stats
    val max_row_length : unit -> int
    val max_row : unit -> form * (t * bool) list
    val clear_cache : unit -> unit
    val reset_stats : unit -> unit
    val	print_cache : out_channel -> unit
    val	store_persistent_cache : unit -> unit
  end


module Make (L : Lattice) : CachedDecider with type t = L.t =
  struct
    type t = L.t
	  
    let res_cache : (form * t * (t -> form) * bool) FormHashtbl.t = FormHashtbl.create 10000

    let clear_cache () =
      FormHashtbl.clear res_cache

    let calls = ref 0
    let cache_hits = ref 0
    let total_time = ref 0.0
    let total_dp_time = ref 0.0
    let max_time = ref 0.0
    let max_query = ref mk_unit

    let max_learning_attempts = ref 0
    let learn_min_length = ref 4

    let filter_chains = Hashtbl.create 0

    let register_filter = 
      Hashtbl.add filter_chains 

    (* Rewrite rule for TPTP conversion *)
    let rewrite_tptp : rewriteRule =
      let r call_back replace_map pol genv env f =
	let mk_res f = (f, []) in
	let rewrite f =
	  match f with
	  | App (Const Elem, [elem; TypedForm (Var set, _)])
	  | App (Const Elem, [elem; Var set]) ->
	      let args = match elem with
	      | App (Const Tuple, ts) -> ts
	      | _ -> [elem]
	      in App (Var set, args)
	  | App (Const Lt, args) -> App (Var "lt", args)
	  | App (Const LtEq, args) -> App (Var "lteq", args)
	  | App (Const Gt, args) -> App (Var "gt", args)
	  | App (Const GtEq, args) -> App (Var "gteq", args)
	  | _ -> f 
	in mk_res (rewrite f)
      in (r, RewriteAtoms)
	
    (** test whether the given sequent is not valid *)
    let test_notvalid env sq0 =
      let max_size = 2 in
      (* eliminate free variables *)
      let sq = elim_fv_in_seq false sq0 in
      (* rewrite tree predicate *)
      let f0 = form_of_sequent sq in
      let f1, _ = TermRewrite.rewrite true 
	  [rewrite_function_eq;
	   rewrite_tree]
	  env (TypeReconstruct.disambiguate f0)
      in
      (* instantiate rtrancl_pt for max. model size *)
      let pn, xn = (Util.fresh_name "p", Util.fresh_name "x") in
      let p = mk_var pn in
      let mk_step xn yn = 
	let x = mk_var xn
	and y = mk_var yn
	in mk_or [mk_eq (x, y); App (p, [x; y])] 
      in
      let rec mk_path i (yn, zs, path) =
	if i <= 0 then (yn, List.tl zs, path) else
	let zn = Util.fresh_name "z" in
	mk_path (i - 1) (zn, zn::zs, mk_step yn zn::path)
      in
      let yn, zns, path = mk_path (max_size - 1) (xn, [], []) in
      let rtrancl_pt = 
	Binder(Lambda, [(pn, TypeUniverse); (xn, TypeUniverse); (yn, TypeUniverse)],
	       smk_exists (List.map (fun zn -> (zn, TypeUniverse)) zns, mk_and path))
      in
      let f2 = subst [(str_rtrancl, rtrancl_pt)] f1 in 
      let f3, env = TermRewrite.rewrite false 
	  [rewrite_sets;
	   rewrite_FieldRead_FieldWrite]
	  env (unlambda f2)
      in 
      (* let f4, env = TypeReconstruct.reconstruct_types env f3 in *)
      let f5, _ = TermRewrite.rewrite false [rewrite_tptp] env f3
      in
      let sqob = 
	{sqob_pos = Common.unknown_pos; 
	 sqob_purpose = ""; 
	 sqob_sq = sequent_of_form (reduce f5)}
      in
      try
	TptpPrettyPrinter.decide_sq sqob ~prover:TptpPrettyPrinter.Paradox ~options:StringMap.empty (* TOFIX : empty is probably not what you want *)
      with _ -> None

    let mk_sqob sq = 
      {sqob_pos = Common.unknown_pos; 
       sqob_purpose = ""; 
       sqob_sq = sq}

    let mona_fast_options = Common.map_of_list
	[("TimeOut", "10");
	 ("QuantInst", "no");
	 ("KeepSpecVars", "yes")]

    let mona_options = Common.map_of_list
	[("TimeOut", "30");
	 ("QuantInst", "no");
	 ("KeepSpecVars", "yes")]

    let cvcl_options = Common.map_of_list
	[("TimeOut", "2");
	 ("MaxQuantInst", "300");
	 ("KeepRtrancl", "yes");
	 ("TryHeuristics", "no")]

    let z3_fast_options = Common.map_of_list
	[("TimeOut", "2");
	 ("KeepRtrancl", "no");
	 ("TryHeuristics", "no")]

    let z3_options = Common.map_of_list
	[("TimeOut", "2");
	 ("KeepRtrancl", "yes");
	 ("TryHeuristics", "no")]

    let spass_options = Common.map_of_list
	[("TimeOut", "5");
	 ("MemoryLimit", "800000000");
	 ("SpassSortGuards", "no");
	 ("KeepRtrancl", "yes");
	 ("Quiet", "yes")]

    let bapa_options = Common.map_of_list
	[("TimeOut", "10");
	 ("fullbapa", "yes");
	 ("SliceQuantAssms", "yes")]

    let paradox_options = Common.map_of_list
	[("TimeOut", "2"); ("Splitting", "no")]

    let fast_provers = 
      let accept_all env sq = true in
      [[("mona", accept_all,
	 ("MONA", fun env sq -> Mona.prove_sequent mona_fast_options env sq))];
       [("cvcl", accept_all,
	 ("CVC lite", fun env sq -> SmtCvcl.cvcl_prove !CmdLine.callbohne sq cvcl_options));
       ("z3", accept_all,
	("Z3", fun env sq -> SmtCvcl.z3_prove !CmdLine.callbohne sq z3_fast_options));
	("spass", accept_all,
	 ("SPASS", fun _ sq -> SpassPrettyPrinter.decide_sq (mk_sqob sq) spass_options));]]
	
    let provers = 
      let accept_all env sq = true in
      [[("bapa", Bapa.is_useful_dp,
	 ("BAPA", fun env sq -> Bapa.decide_sq env (mk_sqob sq) !calls bapa_options))];
       [("card", Cardinality.is_useful_dp,
	 ("SCP", fun _ sq -> Cardinality.decide_sq sq))];
       [("mona", accept_all,
	 ("MONA", fun env sq -> Mona.prove_sequent mona_options env sq))];
       [("z3", accept_all,
	 ("Z3", fun env sq -> SmtCvcl.z3_prove !CmdLine.callbohne sq z3_options));
	(*("z3rtrancl", accept_all,
	 ("Z3", fun env sq -> SmtCvcl.z3_prove !CmdLine.callbohne sq z3_options));*)
	("cvcl", accept_all,
	 ("CVC3", fun env sq -> SmtCvcl.cvcl_prove !CmdLine.callbohne sq cvcl_options));
	("paradox", accept_all,
	 ("Paradox", fun env sq -> 
	   TptpPrettyPrinter.decide_sq (mk_sqob sq) ~prover:TptpPrettyPrinter.Paradox ~options:paradox_options));
	("spass", accept_all,
	 ("SPASS", fun _ sq -> SpassPrettyPrinter.decide_sq (mk_sqob sq) spass_options));
      ]]
	
    (* TOFIX : this is a hack *)
    let usedps () = fst (List.split !CmdLine.usedps)
      
    let dispatch_provers fast env sq =
      [("Jahob", fun _ sq -> test_valid sq)] ::
      List.fold_right (fun provers acc ->
	let provers' = 
	  Util.filter_map (fun (id, is_useful, _) -> 
	    (Util.empty (usedps ()) || List.mem id (usedps ()))
	      && (Util.empty !CmdLine.excludedps || not (List.mem id !CmdLine.excludedps))
	      && is_useful env sq)
	    (fun (id, _, (name, prover)) -> 
	      let filter_chain = Hashtbl.find_all filter_chains id in 
	      (name, fun env sq -> prover env (List.fold_left (fun sq filter -> filter env sq) sq filter_chain)))
	    provers
	in if provers' = [] then acc else provers' :: acc) 
	(if fast then fast_provers else provers) []
 
    let measure_time f arg =
      let start_utime, start_cutime = 
	let ptime = Unix.times () in
	ptime.Unix.tms_utime, ptime.Unix.tms_cutime  
      in
      try 
	let res = f arg in 
	let end_utime, end_cutime = 
	  let ptime = Unix.times () in
	  ptime.Unix.tms_utime, ptime.Unix.tms_cutime  
	in
	total_time := !total_time +. (end_utime -. start_utime) +. (end_cutime -. start_cutime); 
	res
      with e -> 
	let end_utime, end_cutime = 
	  let ptime = Unix.times () in
	  ptime.Unix.tms_utime, ptime.Unix.tms_cutime  
	in
	total_time := !total_time +. (end_utime -. start_utime) +. (end_cutime -. start_cutime); 
	raise e
	
    let normalize f =
      let env0 = get_annotated_types f in
      let fv_f = fv f in
      let unknown = Util.difference fv_f (List.rev_map fst env0) in
      let env = List.fold_left (fun acc v -> (v, TypeUniverse) :: acc) env0 unknown in
      (* let f, env = measure_time (TypeReconstruct.reconstruct_types env0) f in *)
      let sq = sequent_of_form f in
      sq, env

    let reduce_query concr_context f =
      let sq = sequent_of_form (smk_impl (concr_context, f)) in      
      let sq' = elim_fv_in_seq false sq in
      let f' = reduce (unlambda (form_of_sequent sq')) in
      let rec simplify = function
	  | App (Var rtrancl, [f; t1; t2])
	    when rtrancl = str_rtrancl && equal t1 t2 
	    -> mk_true  
	  | App (Const Eq, [Const (IntConst i1); Const (IntConst i2)]) -> 
	      Const (BoolConst (i1 = i2))
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
      in simplify f'

    let cache_result concr_context (context, fn) env f status = 
      let _ =  debug_msg 0 (fun chan ->
	Printf.fprintf chan "Caching formula %d:\n" !calls;
	output_string chan 
	  (PrintForm.string_of_form (strip_types (reduce_query concr_context f)) ^ "\n\n"))
      in
      let res, _ = PersistentCache.result_from_status status in
      FormHashtbl.add res_cache f (concr_context, context, fn, res);
      PersistentCache.insert_query env (smk_impl (concr_context, f)) status

    let find_cached_result concr_context (context, fn) env f =
      try 
	let cached = FormHashtbl.find_all res_cache f in
	let res = Util.find_map 
	    (fun (concr_context', context', fn', res) ->
	      if equal concr_context concr_context' then Some res
	      else if res then
		if L.le context context' && equal concr_context (fn' context)
		then Some res else None
	      else 
		if L.le context' context && equal concr_context (fn' context)
		then Some res else None
	    ) cached
	in
	debug_msg 0 (fun chan ->
	  output_string chan "Cache hit in non-persistent cache.\nFormula is ";
	  output_string chan (if res then "valid." else "not valid."));
	res
      with Not_found -> 
	let status = PersistentCache.find_query env (smk_impl (concr_context, f)) in
	let res, id = PersistentCache.result_from_status status in 
	if id = "Cache" then FormHashtbl.add res_cache f (concr_context, context, fn, res);
	debug_msg 0 (fun chan ->
	  output_string chan "Cache hit in persistent cache.\nFormula is ";
	  output_string chan (if res then "valid." else "not valid."));
	res	
	  

    let decide_form provers env sq =
      let prover_ids = List.fold_left (fun ids provers ->
	List.map fst provers @ ids) [] provers
      in
      let start_time = (Unix.times ()).Unix.tms_cutime in
      let prove_concurrently provers =
	let create_process (num, pid_chans) (prover_id, prover) =
	  let pid, inchan, outchan = UnixUtil.fork_in_out () in
	  match pid with 
	  | 0 (* child process for prover *) ->
	      close_in inchan;
	      let res_opt = try prover env sq with _ -> None in
	      Marshal.to_channel outchan res_opt [];
	      flush outchan;
	      (* close_out outchan; *)
	      exit 0	    
	  | _ (* parent process monitoring all provers *) ->
	      close_out outchan;
	      succ num, (pid, (prover_id, inchan)) :: pid_chans
	in
	let num_of_provers, pid_chans = List.fold_left create_process (0, []) provers in
	let rec wait_for_result finished =
	  if finished = num_of_provers then None else
	  let pid, term_stat = Unix.wait () in
	  try
	    let prover_id, inchan = List.assoc pid pid_chans in
	    match term_stat with
	    | Unix.WEXITED 0 (* prover terminated normally *) ->
		(match (Marshal.from_channel inchan : bool option) with
		| None -> wait_for_result (finished + 1)
		| Some res -> Some (res, prover_id))
	    | _ -> wait_for_result (finished + 1)
	  with 
	  | Not_found -> wait_for_result finished
	in
	let res = wait_for_result 0 in
        (* kill all prover processes and cleanup resources *) 
	let _ = List.iter (fun (pid, (_, inchan)) ->
	  (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ()); 
	  close_in inchan) pid_chans
	in res
      in
      let status =
	try 
	  let res, prover_id = 
	    Util.find_map 
	      (fun provers ->
		if !CmdLine.concurrent_provers then prove_concurrently provers
		else 
		  try
		    Some (Util.find_map (fun (prover_id, prover) ->
		      Util.some_apply (fun res -> (res, prover_id)) (prover env sq)) provers)
		  with Not_found -> None
	      ) provers
	  in PersistentCache.KnownStatus (res, prover_id)
	with Not_found -> PersistentCache.UnknownStatus prover_ids
      in
      let time = (Unix.times ()).Unix.tms_cutime -. start_time in
      total_dp_time := !total_dp_time +. time;
      if time > !max_time then 
	(max_time := time; 
	 let sq' = elim_fv_in_seq false sq in
	 let f = unlambda (strip_types (form_of_sequent sq')) in
	 max_query := f);
      let _ = debug_msg 0 (fun chan ->
	let res, prover_id = PersistentCache.result_from_status status in
	if res then Printf.fprintf chan "formula is valid (%s %.2fs)\n\n" prover_id time 
	else Printf.fprintf chan "formula is not valid (%s %.2fs)\n\n" prover_id time)
      in
      status
      
    let decide_and_cache fast (context, fn) f =
      let d () =
	let _ = incr calls in 
	let sq_f = sequent_of_form f in
	let _ = debug_msg 0 (fun chan ->
	  Printf.fprintf chan "Checked formula %d:\n" !calls;
	(* let asms, conc = elim_fv_in_seq [] sq in
	   let f = unlambda (FormUtil.normalize (-1) (form_of_sequent (asms, negation_normal_form (unlambda conc)))) in *)
	  let sq, _ = normalize (smk_impl (fn context, f)) in
	  output_string chan 
	    (PrintForm.string_of_form (strip_types (form_of_sequent sq)) ^ "\n"))
	in
	let prover sq_f =
	  let f = form_of_sequent sq_f in
	  let cached_sq, sigma = elim_free_vars false [] sq_f in
	  let concr_context = subst sigma (fn context) in
	  let cached_fn c = subst sigma (fn c) in 
	  let sq, env = normalize (smk_impl (concr_context, f)) in
	  let cached_f0 = negation_normal_form (unlambda (form_of_sequent cached_sq)) in
	  let cached_f, _ = (*TypeReconstruct.reconstruct_types env*) cached_f0, env in
	  try
	    let res = 
	      if !CmdLine.usecaching then
		find_cached_result concr_context (context, cached_fn) env cached_f
	      else raise Not_found
	    in incr cache_hits; res
	  with Not_found ->
	    let provers = dispatch_provers fast env sq in
            let status = decide_form provers env sq in
	    let res, _ = PersistentCache.result_from_status status in
	    if !CmdLine.usecaching then cache_result concr_context (context, cached_fn) env cached_f status; 
	    res
	in
	prover sq_f 
      in
      measure_time d ()
 
    (** [decide (context, fn) f] checks whether [fn context] entails [f]. 
       For soundness [fn] must be monotone. *)
    let decide = decide_and_cache false

    (** [decide_fast (context, fn) f] same as decide but potentially (more) incomplete. *)
    let decide_fast = decide_and_cache true
	 

    let stats () =
      { calls = !calls;
	cache_hits = !cache_hits;
	total_time = !total_time;
	total_dp_time = !total_dp_time;
	max_time = !max_time;
	max_query = !max_query
      }	
      
    let print_cache chan =
      let print_row f _ acc =
	if not (List.mem f acc) then
	  begin
	    let row = FormHashtbl.find_all res_cache f in
	    output_string chan "===============\nNew cache row:\n===============\n";
	    List.iter (fun (concr_context, context, fn, res) ->
	      let f' = reduce_query concr_context f in
	      output_string chan (PrintForm.string_of_form (smk_impl (concr_context, f)) ^ "\n");
	      output_string chan (PrintForm.string_of_form f' ^ "\n");
	      if res then output_string chan "Valid\n\n"
	      else output_string chan "Not valid\n\n") row; 
	    f::acc
	  end
	else acc
      in
      ignore (FormHashtbl.fold print_row res_cache [])

    let store_persistent_cache () =
      (* minimize cache entries *)
      let minimize_query key e =
	let res, prover_id = result_from_status e.status in
	if not res || e.minimized || prover_id = "Jahob" then () else
	let query = e.orig_query in
	let sq, env = normalize query in
	let assms, conc = elim_fv_in_seq false sq in
	let prover = List.fold_left (fun acc provers ->
	  List.fold_left (fun acc (_, _, (id, prover)) -> 
	    if id = prover_id then (id, prover) :: acc else acc) acc provers) [] provers
	in
	let check sq =
	  let status = decide_form [prover] env sq in
	  let res, _ = result_from_status status in
	  res
	in
	let rec minimize acc = function
	  | [] -> if check (acc, mk_false) then (acc, mk_false) else (acc, conc)
	  | hyp :: assms -> 
	      if check (acc @ assms, conc) then
		minimize acc assms
	      else minimize (hyp :: acc) assms
	in
	let min_sq = minimize [] assms in
	PersistentCache.insert_minimized env e.orig_query (form_of_sequent min_sq) e.status;
      in
      PersistentCache.iter minimize_query; 
      let filter e = 
	let res, id = result_from_status e.status in
	not res || e.minimized && id <> "Jahob"
      in
      PersistentCache.store_cache filter 
	
      
    let reset_stats () =
      calls := 0; 
      cache_hits := 0;
      total_time := 0.0;
      total_dp_time := 0.0;
      max_time := 0.0;
      max_query := mk_true

    let max_row_length () = 
      let length f _ curr_max = 
	let row = FormHashtbl.find_all res_cache f in
	max curr_max (List.length row)
      in
      FormHashtbl.fold length res_cache 0

    let max_row () =
      let res = ref (mk_true, []) in
      let max_length = max_row_length () in
      FormHashtbl.iter (fun f _ ->
	let row = FormHashtbl.find_all res_cache f in
	if List.length row = max_length then
	  res := (f, List.map (fun (_, c, _, res) -> (c, res)) row)) res_cache;
      !res
  end
