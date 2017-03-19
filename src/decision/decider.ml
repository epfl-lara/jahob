(** Decision procedure dispatcher. *)
open Printf
open Common
open Form
open FormUtil
open PrintForm
open SmtCvcl
open TermRewrite
open MonaConvert
open TypeReconstruct
open Slice
open TptpPrettyPrinter

(** Debug messages **)
let debug_lmsg = Debug.debug_lmsg (Debug.register_debug_module "Decider")

let stats : ('a , (int*int*float)) Hashtbl.t= Hashtbl.create 10

let incr_prover_stat (prover : string) (options:options_t) (successful : bool) (time:float) : unit = 
  let (total, success, acc_time) = try Hashtbl.find stats (prover,options) with Not_found -> (0, 0, 0.0) in
    Hashtbl.replace stats (prover,options) 
      (total+1, (success + if successful then 1 else 0), (acc_time +. time))

let clear_stats () = Hashtbl.clear stats

let sequents_attempted = ref 0
let sequents_verified = ref 0
let methods_attempted = ref 0
let methods_verified = ref 0

let clear_summary () : unit =
  sequents_attempted := 0;
  sequents_verified := 0;
  methods_attempted := 0;
  methods_verified := 0

let print_summary () : unit =
  Printf.printf "\nVerified %d of %d methods and %d of %d sequents."
    !methods_verified !methods_attempted !sequents_verified !sequents_attempted 

let start (name : string) : unit =
  clear_stats ();
  Isabelle.start name;
  Coq.start name;
  TptpPrettyPrinter.start name

let refresh (v : ident) (f : form) : form =
  nsubst [(v,mk_var (Util.fresh_name v))] f 
    (** can call nsubst because it's fresh *)

(* This procedure returns true if the proof obligation is found among the assumptions. *)
let trivially_true ((assumptions, po) : sequent) : bool =
  let rec trivially_true_rec (al0 : form list) (po0 : form) : bool =
    match al0 with
      | [] -> false
      | a0 :: arest -> 
	  let a1 = FormUtil.remove_comments (FormUtil.remove_typedform a0) in
	  let trivial = equal a1 po0 in
	  if trivial && not !CmdLine.callbohne then
	    Util.msg "Trivially true.\n";
	  trivial || (trivially_true_rec arest po0)
  in
  let po0 = FormUtil.remove_comments (FormUtil.remove_typedform po) in
  (trivially_true_rec assumptions po0)

(* Simple syntactic validity checker *) 
let test_valid ((asms, conc) : sequent) : bool option =
  let rec le f1 f2 = match (f1, f2) with
    (* Reachability *)
    | (Const (BoolConst false), _) -> true
    | (_, Const (BoolConst true)) -> true


    | (_, App (Const Not, [App (Const Eq, [Const IntConst i; Const IntConst j])])) -> not (i = j)
    | (_, App (Const Eq, [Const IntConst i; Const IntConst j])) -> i = j  
    | (_, App (Const Eq, [t1; t2]))
    | (_, App (Const LtEq, [t1; t2])) when equal t1 t2 -> true

      (* f1 --> rtrancl_pt r t t *)
    | (_, App (Var "rtrancl_pt", [_; t1; t2])) 
      when equal t1 t2 -> true
    | (App (Const Eq, [t1'; t2']), App (Var "rtrancl_pt", [_; t1; t2])) 
      when (equal t1 t1' && equal t2 t2' || equal t1 t2' && equal t2 t1') -> 
	true 
    | (App (Const Eq, [t1'; t2']), App (Var "rtrancl_pt", [r; t1; t2])) ->
	(match r with
	| Binder (Lambda, [(v1, _); (v2, _)], f) ->
	    le f1 (subst [(v1, t1); (v2, t2)] f)
	| _ -> false)
    | (App (Var "rtrancl_pt", [r; t1; t2]), App (Var "rtrancl_pt", [r'; t1'; t2'])) ->
	equal r r' && equal t2 t2' && (equal t1 t1' ||
	match r' with 
	| Binder (Lambda, [(v1, _); (v2, _)], f) ->
	    le (mk_eq (t1, mk_var v2)) (subst [(v1, t1')] f)
	| _ -> false)

    (* Equality *)
    | (App (Const Eq, _), App (Const LtEq, [t21;t22])) 
    | (App (Const Eq, _), App (Const Not, [App (Const Lt, [t21;t22])])) ->
	le f1 (App (Const Eq, [t21;t22]))
    | (App (Const Lt, [t21;t22]), App (Const Not, [App (Const Eq, _) as f2']))
	-> le f2' (App (Const Eq, [t21;t22]))	      
    | (App (Const Eq, [t11;t12]), App (Const Eq, [t21;t22])) ->
	(equal t21 t22 || equal t11 t21 && equal t12 t22 || equal t11 t22 && equal t12 t21) || 
	begin
	  match (t11, t12, t21, t22) with
	  | (App (f1, [t1]), App (f2, [t2]), _, _) when equal f1 f2 ->
	      le (App (Const Eq, [t1;t2])) f2
	  | (_, _, App (f1, [t1]), App (f2, [t2])) when equal f1 f2 ->
	      le (App (Const Eq, [t1;t2])) f1
	  |	_ -> false
	end   
	
    (* Boolean operators *)

    | (App (Const And, conj), _) ->
	List.exists (fun c -> le c f2) conj
	  
    | (_, App (Const And, conj)) ->
	List.for_all (fun c -> le f1 c) conj
	  
    | (_, App (Const Not, [App (Const And, conj)])) ->
	List.exists (fun d -> le f1 (mk_not d)) conj
	  
    | (_, App (Const Or, disj)) ->
	List.exists (fun d -> le f1 d) disj
	  
    |  (App (Const Not, [f1']), App (Const Not, [f2'])) ->
	 le f2' f1'
	   
    (* Quantifiers *)
    | (Binder (Exists, [(v,t)], f1'), _) -> le (refresh v f1') f2
    | (_, Binder (Forall, [(v,t)], f2')) -> le f1 (refresh v f2')
    | (Binder (b1, [(v1, t1)], f1'), Binder (b2, [(v2, t2)], f2'))
	when b1 = b2 && normalize_type t1 = normalize_type t2 && v1 = v2 -> le f1' f2'
    | _ -> equal f1 f2	   
  in
  let result = (trivially_true (asms, conc)) ||
      (let asms, conc = elim_fv_in_seq false (asms, conc) in
       let asms = negation_normal_form (unlambda (normalize (-1) (mk_and asms))) in
       let conc = negation_normal_form (unlambda (normalize (-1) conc)) in

       let asms = FormUtil.remove_comments (FormUtil.remove_typedform asms) in
       let conc = FormUtil.remove_comments (FormUtil.remove_typedform conc) in

	 le asms conc)
  in
  (* let _ = if result then Util.msg "e" in *)
  if result then Some true else None
     
let first_order_proved = ref None 

let built_in_name_initial = "Built-in validity checker (during splitting)"
let built_in_name_later = "Built-in validity checker (after splitting)"
let proven_lemmas_name = "Lemma file"

let provers = 
  [("test_valid",
    (built_in_name_later,
    fun _ _ sqob _ -> test_valid sqob.sqob_sq));
   ("proven_lemmas",
    (proven_lemmas_name,
     fun _ _ sqob _ -> Isabelle.check_proven_lemmas sqob));
   ("mona", 
    ("MONA",
     fun env _ sqob options ->
	slice_and_prove 
	 [slice_default; slice_obj_vars; slice_obj_sets] 
	 env (Mona.prove_sequent options env) sqob.sqob_sq));
   ("e", 
    ("E", 
     fun _ k sqob options -> 
       let r = TptpPrettyPrinter.decide_sq sqob ~prover:E ~options in
       let _ = if Util.safe_unsome false r then first_order_proved := Some ("e", Common.string_of_options options) in
	 r
    )) ;  
   ("vampire", 
    ("Vampire", 
     fun _ k sqob options -> 
       let r = TptpPrettyPrinter.decide_sq sqob ~prover:Vampire ~options in
       let _ = if Util.safe_unsome false r then first_order_proved := Some ("vampire", Common.string_of_options options) in
	 r
    )) ;
   ("spass", 
    ("SPASS", 
     fun _ k sqob options -> 
       let r : bool option = SpassPrettyPrinter.decide_sq sqob ~options in
       let _ = if Util.safe_unsome false r then first_order_proved := Some ("spass", Common.string_of_options options) in
	 r
    )) ;
   ("cvcl", 
    ("CVC3", 
     fun _ _ sqob options -> cvcl_prove false sqob.sqob_sq options));
   ("z3", 
    ("Z3", 
     fun _ _ sqob options -> z3_prove false sqob.sqob_sq options));
   ("isa", 
    ("Isabelle", 
     fun _ k sqob options -> Isabelle.decide_sq sqob k ~options));
   ("coq", 
    ("Coq", 
     fun _ k sqob options -> Coq.decide_sq sqob k ~options)) ;
   ("paradox", 
    ("Paradox", 
     fun _ k sqob options -> TptpPrettyPrinter.decide_sq sqob ~prover:Paradox ~options));
   ("bapa", 
    ("BAPA", 
     fun env k sqob options -> Bapa.decide_sq env sqob k ~options));
   ("card",
    ("Simple cardinality prover",
     fun _ _ sqob _  -> Cardinality.decide_sq sqob.sqob_sq))
  ]

let default_prover_choice = 
  ListLabels.map ~f:(fun (name, _) -> (name, StringMap.empty)) provers

(*
let _ = if (List.map fst provers) != CmdLine.prover_names then
  Util.fail "Error in decider.ml: prover names in command line are not up to date."
*)

let used_provers () : (string * options_t) list =
  let usedps = !CmdLine.usedps in
    if usedps = [] then
      default_prover_choice
    else
      let vchecker = ("test_valid", StringMap.empty) in
	if (List.exists (fun (x, _) -> x = "isa") usedps) then
	  vchecker :: ("proven_lemmas", StringMap.empty) :: (List.rev usedps)
	else 
	  vchecker :: (List.rev usedps)

let separator = "======================================================================\n"

let print_stats (count_method : bool) = 
  let paren s = if s = "" then "" else " (" ^ s ^ ")" in
  let eliminated = try let (_,elim,_) = 
    (Hashtbl.find stats (built_in_name_initial, StringMap.empty)) in 
    elim with Not_found -> 0 in
  let acc_s = ref eliminated in
  let total = eliminated + try let (r,_,_) = 
    (Hashtbl.find stats (built_in_name_later, StringMap.empty)) in 
    r with Not_found -> 0 in
  if total > 0 then begin  
    print_string "\n"; print_string separator;
    (if eliminated > 0 then
      Printf.printf 
	"Built-in validity checker proved %d sequents during splitting.\n" 
	eliminated);
    List.iter (fun (prover, options) -> 
		 let prover_name, _ = List.assoc prover provers in
		 let (total, success, time) = try Hashtbl.find stats (prover_name, options) with Not_found -> (0, 0, (0.)) in
		 let time1 = 
		   if time < 0. then (time -. 0.05) else (time +. 0.05) in
		   (if success > 0 || time1 >= 0.1 then 
		     Printf.printf "%s%s proved %d out of %d sequents. Total time : %.1f s\n" prover_name (paren (Common.string_of_options options)) 
		       success total time1);
		   acc_s := !acc_s + success) (used_provers ());
    print_string separator;
    sequents_attempted := !sequents_attempted + total;
    sequents_verified := !sequents_verified + !acc_s;
    if count_method then 
      (methods_attempted := !methods_attempted + 1;
       if !acc_s = total then
	 methods_verified := !methods_verified + 1);
    Printf.printf "A total of %d sequents out of %d proved.\n" !acc_s total
  end

let stop (count_method : bool) : unit = 
  Isabelle.stop () ;
  Coq.stop () ;
  print_stats (count_method) 

(** Print and parse formula again.
    Used for debugging; should not be necessary. *)
let reparse (f : form) : form = 
  let formula_string = 
    PrintForm.string_of_form f in
    ParseForm.parse_formula formula_string

let test_valid_stat ((asms,f) : sequent) : bool =
  let res_opt = test_valid (asms,f) in
  let res = Util.safe_unsome false res_opt in
  let _ = 
    if res then 
      Util.msg ("Proved during splitting: " ^ string_of_sequent (asms,f) ^ "\n")
  in
    incr_prover_stat built_in_name_initial StringMap.empty res 0.0;
    res

let filter_using_hints (asms : form list) (goal : form) : (form list * form) =
  match (FormUtil.strip_types goal) with
    | App(Const Comment,[Const (StringConst s);f]) ->
	(match decode_hints s with
	   | None -> (asms,goal)
	   | Some (hs,msg) -> 
	       (List.filter (FormUtil.is_hinted hs) asms, mk_comment msg f)
	)
    | _ -> (asms,goal)

let generate_sequents (env:typeEnv) (f:form) : sequentenv list =
  let rec add (hyps : (form * string) list) (asms : form list) = match hyps with
    | [] -> asms
    | (App(Const And,fs),c)::hyps1 -> add ((List.map (fun f -> (f,c)) fs) @ hyps1) asms
    | (App(Const MetaAnd,fs),c)::hyps1 -> add ((App(Const And,fs),c)::hyps1) asms
    | (App(Const Comment,[Const (StringConst c);h]),c0)::hyps1 -> 
	add ((h,c ^ c0)::hyps1) asms
    | (hyp,c)::hyps1 -> add hyps1 (mk_comment c hyp::asms)
  and add_one hyp asms = add [(hyp,"")] asms
  in
  let rec gen comments env asms f acc = 
    let add_comment (f0 : form) : form =
      mk_comment (remove_hints (String.concat "_" comments)) f0 in
    let add_comment_with_hints (f0 : form) : form =
      mk_comment (String.concat "_" comments) f0 in
    if test_valid_stat (asms,f) then acc
    else match f with
      | App(Const Comment,[Const (StringConst c);f1]) -> gen (c::comments) env asms f1 acc
      | App(Const Impl,[f1;f2]) -> gen comments env (add_one (add_comment f1) asms) f2 acc
      | App(Const MetaImpl,[f1;f2]) -> gen comments env (add_one (add_comment f1) asms) f2 acc
      | App(Const And,fs) -> gens comments env asms fs acc
      | App(Const MetaAnd,fs) -> gens comments env asms fs acc
      | Binder(Forall,[],f1) -> gen comments env asms f1 acc
      | Binder(Forall,(v,t)::vts,f1) -> 
	  (let v1 = Util.fresh_name v in
	   let f1r = nsubst [(v,mk_var v1)] f1 in (** can call nsubst on fresh v1 *)
	     gen comments ((v1,t) :: env) asms (Binder(Forall,vts,f1r)) acc)
      | _ -> 
	  (let cf = add_comment_with_hints f in
	     ((filter_using_hints (List.rev asms) cf), env)::acc)
  and gens comments env asms fs acc = List.fold_right (gen comments env asms) fs acc
  in 
  let res = gen [] env [] f [] in
  res

let exc_to_bool (prover : string) (f : 'a -> bool option) (x : 'a) : bool option =
  let failed_with exn = 
    Util.msg ("Prover '" ^ prover ^ "' failed with " ^ exn ^ ".\n");
    None
  in try f x with e -> failed_with (Printexc.to_string e)

let get_min_sq
    prover
    (env : typeEnv)
    (goal : form) 
    (asms : form list) : form list =
  let rec get_min_sq asms (useful_asms : form list) =
    match asms with
    | [] -> useful_asms
    | f::asms1 ->
	let sqob = 
	  {sqob_pos = Common.unknown_pos; 
	   sqob_purpose = ""; 
	   sqob_sq = (List.rev_append useful_asms asms1, goal)}
	in 
	if Util.safe_unsome false (prover sqob)
	then get_min_sq asms1 useful_asms
	else get_min_sq asms1 (f::useful_asms)
  in get_min_sq asms []

let print_minimal_sequent
    prover
    (env : typeEnv) 
    (sqob : sq_obligation) : unit =
  let asms, goal = sqob.sqob_sq in
  let min_asms = get_min_sq prover env goal asms in
  let min_sq = (List.map strip_types min_asms, strip_types goal) in
    Util.amsg ("\nMinimal sequent is:\n" ^ string_of_sequent min_sq)

let prove_sqob_with ((prover_id : string), (options : options_t))
    (sqob : sq_obligation) (env : typeEnv) (k : int) : bool = 
  let pmsg str =
    if !Util.verbose then Util.msg str 
    else Util.amsg "."
  in
  try
    let name, prover = List.assoc prover_id provers in
    let _ = Util.msg ("Running " ^ name ^ "... ") in
    let now = Unix.gettimeofday () in
    let safe_prover : sq_obligation -> bool option = exc_to_bool name (fun f -> prover env k f options) in
    let res_opt : bool option = safe_prover sqob in
    let res = Util.safe_unsome false res_opt in
    let running_time =  Unix.gettimeofday () -. now in
      incr_prover_stat name options res running_time;
      let _ = match res_opt with 
      |	Some true ->
	  pmsg (name ^ " proved formula.\n");
	  if !CmdLine.minasm 
	  then print_minimal_sequent safe_prover env sqob
      |	Some false ->
	  pmsg (name ^ " found a counter-model for formula.\n")
      |	None ->	pmsg (name ^ " failed to prove formula.\n")
      in res
  with Not_found -> 
    Util.warn ("Unknown prover \"" ^ prover_id ^ "\"");
    false

let seq_count = ref 0

let starting_time = Unix.time ()

let save_sequent (sq:sequent) : unit =
  let vc_string = string_of_sequent sq in
  
  let rec sequent_file_name starting = 
    let r = Util.tmp_name (Printf.sprintf "archive-%.0f_%d_%03d.isa" starting_time starting !seq_count) in
      if Sys.file_exists r then sequent_file_name (starting+1) else r
  in
  let f = open_out (sequent_file_name 0) in
    (match !first_order_proved with
       | None -> assert false
       | Some (p, o) ->
	   output_string f (p ^ "\n");
	   output_string f (o ^ "\n");
    );
    output_string f vc_string;
    close_out f;
    incr seq_count;;


let prove_sqob (sqob : sq_obligation) (env : typeEnv) (k : int) : bool =
  let sq = sqob.sqob_sq in
  let vc_string = string_of_sequent sq in
  let pmsg str =
    Util.msg str; Util.amsg "."
  in
    pmsg ("\nProof obligation: " ^ vc_string ^ "\n");
    first_order_proved := None;
    let used_provers = used_provers () in
    let res = List.exists (fun prover -> prove_sqob_with prover sqob env k) used_provers in
    let _ = (if not res then 
      Util.amsg ("All provers failed on proof obligation: '" ^ extract_comments (snd sq) ^ "'\n")
    else 
      ()) (* (if !first_order_proved <> None then save_sequent sqob.sqob_sq)) *)
    in
      res

let split_in_chunks_of : (int -> 'a list -> 'a list list) =
  fun k xs ->
    let rec split (i : int) acc rest =
      if i <= 0 then (List.rev acc) :: split k [] rest
      else (match rest with
	      | [] -> 
		  (match acc with
		     | [] -> []
		     | _ -> [List.rev acc])
	      | r::rest1 -> split (i - 1) (r::acc) rest1)
    in split k [] xs

type proc_desc = {
  proc_id : int;
  proc_res_chan : in_channel;
}

(** find process of a given id in a given process list *)
let rec find_desc (id : int) (ds : proc_desc list) : 
    (proc_desc option * proc_desc list) =
  match ds with
    | [] -> (None, [])
    | ({proc_id = pid; proc_res_chan = chan} as d)::ds1 ->
	if pid=id then (Some d, ds1)
	else 
	  let (res,ds2) = find_desc id ds1 
	  in (res, d::ds2)

(** Proving proof obligations by spawning threads to prove each chunk *)
let spawn_process ((sq,env) : sequentenv) : proc_desc =
  let read_fdesc, write_fdesc = Unix.pipe() in
  let read_chan = Unix.in_channel_of_descr read_fdesc in
  let write_chan = Unix.out_channel_of_descr write_fdesc in
  let pid = Unix.fork() in
    match pid with 
      | 0 (* child process for prover *) ->
	  let sqob = {
	    sqob_sq = sq;
            sqob_pos = Common.unknown_pos;
            sqob_purpose = "";
	  } in
	  let res_opt = try Some (prove_sqob sqob env 42) with _ -> None in
	    Marshal.to_channel write_chan res_opt [];
	    flush write_chan;
	    close_out write_chan;
	    exit 0
      | _ (* parent process monitoring all provers *) ->
	  { proc_id = pid; 
	    proc_res_chan = read_chan }

let cleanup_process (pd : proc_desc) : unit =
  match pd with 
      { proc_id = pid; proc_res_chan = inchan} ->
	(try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ()); 
	close_in inchan

let prove_chunk sqs failfast : bool = 
  let processes = List.map spawn_process sqs in
  let rec wait_for_result (ds : proc_desc list) (res : bool option) =
    let sequent_failed (rest : proc_desc list) =
      if failfast then (Some false, rest)
      else wait_for_result rest (Some false)
    in
    let pid, term_stat = Unix.wait () in
      match find_desc pid ds with
	| (Some ({proc_res_chan = chan} as d), ds1) ->
 	    (match term_stat with
	       | Unix.WEXITED 0 (* prover terminated normally *) ->
		   let says = (Marshal.from_channel chan : bool option) in
		   let _ = cleanup_process d in
		     (match says with
		      | Some true -> (* proved a sequent *)
			  (match ds1 with
			     | [] -> (Some true,[]) (* proved them all *)
			     | _ -> wait_for_result ds1 res)
		      | _ -> sequent_failed ds1)
	       | _ -> let _ = cleanup_process d in sequent_failed ds1)
	| _ -> wait_for_result ds res
  in
  let (res,leftover_procs) = wait_for_result processes None in
  let _ = List.iter cleanup_process leftover_procs in
    (res = Some true)

let rec prove_all_concurrently 
    (chunks : sequentenv list list) 
    (failfast : bool) : bool =
  match chunks with
    | [] -> true
    | ch::chunks1 -> 
	if prove_chunk ch failfast then 
	  prove_all_concurrently chunks1 failfast
	else if failfast then false
	else (let _ = prove_all_concurrently chunks1 failfast in false)

(* --------------------------------------------------------- *)
(* This part is relevant for splitting a sequent recursively. *)

(* Splits a proof obligation into two or more using distributive law in the antecedent,
   i.e. (f1 or ... or fn)=>h is the same as (f1=>h)and...and(fn=>h). 
   Returns None if no reduction was possible.
   Returns Some [s1;...;sn] if each si is textually smaller than the input and the conjunction of (1<=i<=n) is equivalent to the original obligation.
   Added by AM.
*)
let split_sq_oblig_antecedent_disjunctively (sqob:sq_obligation) (env:typeEnv) (k:int) : (sq_obligation list) option =

  (* Takes a list of formulas rev_prefix, formula f, list of formulas fs, and outputs a simplified version of (reverse(rev_prefix) and f and fs). *)
  let rec simplify rev_prefix f fsl =
    match f with
        App(Const And,[]) -> List.rev_append rev_prefix fsl
      | App(Const MetaAnd,[]) -> List.rev_append rev_prefix fsl
      | App(Const Comment,[Const (StringConst s);App(Const And,[])]) -> List.rev_append rev_prefix fsl
      | App(Const Comment,[Const (StringConst s);App(Const MetaAnd,[])]) -> List.rev_append rev_prefix fsl
      | App(Const And,(g::gs))
      | App(Const MetaAnd,(g::gs)) -> simplify rev_prefix g (gs@fsl)
      | App(Const Comment,[Const (StringConst s);App(Const And,[g])])
      | App(Const Comment,[Const (StringConst s);App(Const MetaAnd,[g])]) 
      | App(Const Comment,[Const (StringConst s);App(Const Or,[g])]) -> 
          simplify rev_prefix (App(Const Comment,[Const (StringConst s);g])) fsl
      | App(Const Comment,[Const (StringConst s);App(Const And,(g::gs))])
      | App(Const Comment,[Const (StringConst s);App(Const MetaAnd,(g::gs))]) ->
          let new_gs=List.fold_left (fun sofar gg -> (App(Const Comment,[Const (StringConst s);gg]))::sofar) [] gs
	  in simplify rev_prefix (App(Const Comment,[Const (StringConst s);g])) (List.rev_append new_gs fsl)
      | _ -> List.rev_append rev_prefix (f::fsl)
  in
  (* Tries to split a formula f into a list of textually smaller f1,...,fn such that f=(f1 or ... or fn). 
     Returns None if no splitting was possible.
     Returns Some [f1;...;fn] if each fi is strictly smaller than f (1<=i<=n).
  *)
  let rec split_form_disjunctively (f:form) : ((form list) option) = match f with
      App(Const Or, disjlist) -> 
        (* Combine formulas like ((a or b) or c) into Some [a;b;c] *)
	let rec walk_disj_list disjlist sofar=
          (match disjlist with
               [] -> sofar
             | (App(Const Or, dsh))::ds -> walk_disj_list (dsh@ds) sofar
             | (App(Const Comment,[(Const(StringConst s));(App(Const Or, dsh))]))::ds -> 
                 let comments_pushed_down=List.fold_left (fun acc g -> ((App(Const Comment,[Const (StringConst s);g]))::acc)) [] dsh
	         in walk_disj_list (comments_pushed_down@ds) sofar
             | d::ds -> (walk_disj_list ds (d::sofar)))
        in Some (walk_disj_list disjlist [])
    | App(Const Comment,[Const (StringConst s);ff]) ->
        (match split_form_disjunctively ff with
             None -> None
           | Some lst -> Some (List.fold_left (fun acc g -> ((App(Const Comment,[Const (StringConst s);g]))::acc)) [] lst))
    | App(Const And,conjlist) ->
        let rec walk_conj_list (fs:form list) (rev_prefix:form list) : ((form list) option) =
          (match fs with
               [] -> None
             | c::cs -> 
                 (match split_form_disjunctively c with
                      None -> walk_conj_list cs (c::rev_prefix)
                    | Some lst -> Some (List.fold_left (fun sofar f -> (App(Const And,(simplify rev_prefix f cs)))::sofar) [] lst)
                 )
          )
        in walk_conj_list conjlist []
    | App(Const MetaAnd,conjlist) ->
        let rec walk_conj_list (fs:form list) (rev_prefix:form list) : ((form list) option) =
          (match fs with
               [] -> None
             | c::cs -> 
                 (match split_form_disjunctively c with
                      None -> walk_conj_list cs (c::rev_prefix)
                    | Some lst -> Some (List.fold_left (fun sofar f -> (App(Const MetaAnd,(simplify rev_prefix f cs)))::sofar) [] lst)
                 )
          )
        in walk_conj_list conjlist []    
    | TypedForm(ff,t) -> 
        (match split_form_disjunctively ff with
             None -> None
           | Some lst -> Some (List.fold_left (fun acc g -> (TypedForm(g,t))::acc) [] lst))
    | _ -> None

  (* Takes a list of formulas fs, interpreted as their conjunction. Any external caller should call this function only with empty rev_prefix.
     Tries to split fs into lists fs1,...,fsn such that fs = (fs1 or ... or fsn).
     Returns None if no reduction was possible.
     Returns Some [fs1;...;fsn] if each fsi represents a strictly smaller formula than fs (1<=i<=n).
  *)
  and split_conj_form_list_disjunctively (fs:form list) (rev_prefix:form list): (((form list) list) option) =
    match fs with
      [] -> None
    | f::fsl ->
       match split_form_disjunctively f with
         None -> split_conj_form_list_disjunctively fsl (f::rev_prefix)
       | Some lst -> Some (List.fold_left (fun acc f -> (simplify rev_prefix f fsl)::acc) [] lst)
  in
   match split_conj_form_list_disjunctively (fst (sqob.sqob_sq)) [] with
      None -> None
    | Some [] -> Some [{sqob_pos=sqob.sqob_pos; sqob_purpose=sqob.sqob_purpose; sqob_sq=([Const (BoolConst false)],(Const (BoolConst true)))}]
    | Some lst -> Some (List.fold_left (fun acc f -> {sqob_pos=sqob.sqob_pos; sqob_purpose=sqob.sqob_purpose; sqob_sq=(f,(snd sqob.sqob_sq))}::acc) [] lst)


(* Tries to prove a sequent first in the original form, after that splitting the antecedent using the distributive law recursively. *)
let prove_sqob_recursively (sqob:sq_obligation) (env:typeEnv) (k:int) =
  let pmsg str =
    Util.msg str; Util.amsg "."
  in let _= (first_order_proved := None)
  in let used_provers=used_provers ()
  (* in let _= Util.msg ("We are using "^(string_of_int (List.length used_provers))^" provers\n") *)
  in let rec prove_sqob_with_provers proverslist sqob env k (prover_results_sofar: (string*options_t*(bool option)*float) list) : bool option =
    let rec walk_through_conjunctive_sqlist = function
        [] -> Some true
      | sq::sqs -> 
          let res=prove_sqob_with_provers used_provers sq env k [] in
          (match res with
               None 
	     | Some false -> res
             | Some true -> walk_through_conjunctive_sqlist sqs
          )
    in
    let inc_stat pr_res_lst = List.iter (fun (name,options,res_opt,running_time) -> (incr_prover_stat name options (Util.safe_unsome false res_opt) running_time)) pr_res_lst
    in
    (match proverslist with
         [] -> 
           let now = Unix.gettimeofday () in
           let res_opt=split_sq_oblig_antecedent_disjunctively sqob env k in
	   let running_time =Unix.gettimeofday() -. now in
           (match res_opt with
               None -> (inc_stat prover_results_sofar; None)
             | Some [] -> (inc_stat prover_results_sofar; (incr_prover_stat built_in_name_later (StringMap.empty) true running_time); (Some true))
             | Some lst -> walk_through_conjunctive_sqlist lst
           )
       | (prover_id,options)::prs ->
         try
           let (name,prover)=List.assoc prover_id provers in
           let now = Unix.gettimeofday () in
           let safe_prover f = prover env k f options in
           let _=Util.msg ("Running "^name^" on the sequent\n"^(string_of_sequent (sqob.sqob_sq))^"\n.") in
           let res_opt = safe_prover sqob in
           let running_time= Unix.gettimeofday() -. now in
             (match res_opt with
                  Some true -> ((inc_stat prover_results_sofar);
				(incr_prover_stat name options true running_time);
		                (Util.msg (name^" proved the formula.\n"));
                                (if !CmdLine.minasm then print_minimal_sequent safe_prover env sqob);
                                res_opt)
                | Some false -> ((inc_stat prover_results_sofar);
				(incr_prover_stat name options false running_time);
		                (Util.msg (name^" found a counterexample for the formula.\n"));res_opt)
                | None -> ((Util.msg (name^" failed to prove the formula.\n"));
			   (prove_sqob_with_provers prs sqob env k ((name,options,res_opt,running_time)::prover_results_sofar)))
             )
         with Not_found -> Util.warn ("Unknown prover \""^prover_id^"\".\n"); None
    )
  in
    let sq = sqob.sqob_sq in
    let _ = pmsg ("\nProof obligation: "^(string_of_sequent sq)^"\n") in
    let res_opt= prove_sqob_with_provers used_provers sqob env k [] in
    ((match res_opt with
         None -> pmsg ("All provers failed on proof obligation '" ^ extract_comments (snd sq) ^ "'\n")
       | Some false -> pmsg "Sequent was shown to be invalid.\n"
       | Some true -> pmsg "Sequent proven.\n"
     ); res_opt)
(* --------------------------------------------------------- *)

let split_and_decide (ob : obligation) (failfast : bool) : bool = 
  let f0 = ob.ob_form in
  let f, env = TypeReconstruct.reconstruct_types [] f0 in
    if !CmdLine.novcsplit then
      let sqob = { 
	sqob_sq = ([],f);
	sqob_purpose = ob.ob_purpose; 
	sqob_pos = ob.ob_pos;
      } in
        if !CmdLine.tryHard then Util.safe_unsome false (prove_sqob_recursively sqob env 0)
        else prove_sqob sqob env 0
    else 
      (let sqs = generate_sequents env f in
       let len = List.length sqs in
       let rec prove_all sqs k = 
	 match sqs with
	   | [] -> true
	   | (sq, env)::sqs1 -> begin	  
               debug_lmsg 0 (fun () -> 
			       (Printf.sprintf "\nProving sequent %d of %d.   " k len));
	       let kstr = Printf.sprintf "%d" k in
	       let sqob = { 
		 sqob_sq = sq;
		 sqob_purpose = ob.ob_purpose ^ kstr; 
		 sqob_pos = ob.ob_pos;
	       } in
	       let ok = if !CmdLine.tryHard 
		 then Util.safe_unsome false (prove_sqob_recursively sqob env k)
                 else prove_sqob sqob env k in
	       if ok then 
		 prove_all sqs1 (k+1)
	       else 
		 (if failfast then false
		  else let _ = prove_all sqs1 (k+1) in false)
	   end
       in
	 if !CmdLine.concurrent_provers && (!CmdLine.maxvcpar > 0) then 
	   prove_all_concurrently 
	     (split_in_chunks_of !CmdLine.maxvcpar sqs) failfast
	 else prove_all sqs 1)
    
let ob_valid (oblig : obligation) (failfast : bool) : bool =
  if !CmdLine.verify then 
    split_and_decide oblig failfast
  else false
    
let valid (f : form) : bool =
  ob_valid (form_to_oblig f) !CmdLine.failfast

let ff_valid (f : form) : bool =
  ob_valid (form_to_oblig f) true

(*
  Bapa.lashIsUnsatisfiable f
  Bapa.valid f 
*)
