(* Dispatch formulas to Z3 via its SMTLIB 2.0 interface. *)

open Common

let debug_id : int = Debug.register_debug_module "SmtZ3"
let debug_msg: (string -> unit) = Debug.debug_msg debug_id
let debug_is_on () : bool = Debug.debug_is_on debug_id

(** [check_z3_results outfile] scans outfile, returning
    - Some false if the result indicates that the formula was unsatisfiable,
    - Some true if the result indicates that the formula was satisfiable,
    - None if the result indicates that nothing could have been shown. *)
let check_z3_results outfile =
  (** [scan sofar_result unsupported_encountered result_determined result_inconclusive] 
      reads the remainder of the outfile to determine the result of the satisfiability checking.
      The arguments provide the information gathered from the previous lines:
      - sofar_result should be Some true or Some false if sat/unsat has been encountered, or None in all other cases;
      - unsupported_encountered should be true if "unsupported" has been encountered, false otherwise;
      - result_determined should be true if sat/unsat/unknown has been encountered;
      - result_inconclusive should be true if two different results from {sat,unsat,unknown} have been seen.
      The function prints diagnostics in the debug mode.
      Returns
    - Some false if the result indicates that the formula was unsatisfiable,
    - Some true if the result indicates that the formula was satisfiable,
    - None if the result indicates that nothing could have been shown. *)
  let rec scan sofar_result unsupported_encountered result_determined result_inconclusive =
    (try
       let line = input_line outfile in
       if line = "unsat" then
	 match sofar_result with
	     Some false -> scan sofar_result unsupported_encountered true result_inconclusive
	   | Some true -> scan None unsupported_encountered true true
	   | None -> 
	     if result_determined then scan None unsupported_encountered error_encountered true true
	     else scan (Some false) unsupported_encountered true result_inconclusive
       else if line = "sat" then
	 match sofar_result with
	     Some false -> scan None unsupported_encountered true true
	   | Some true -> scan sofar_result unsupported_encountered true result_inconclusive
	   | None -> 
	     if result_determined then scan None unsupported_encountered true true
	     else scan (Some true) unsupported_encountered true result_inconclusive
       else if line = "unknown" then
	 match sofar_result with
	     Some _ ->  scan None unsupported_encountered true true
	   | None -> scan None unsupported_encountered true result_inconclusive
       else if line = "unsupported" then
	 let unsupported_line = input_line outfile in
	 ((if not unsupported_encountered then debug_msg ("Z3 does not support: "^unsupported_line^".\n"));
	  scan sofar_result true result_determined result_inconclusive)
       else if (Util.string_starts_with_string line "WARNING: ") then
	 (debug_msg ("Z3: "^line^".\n");
	  scan sofar_result unsupported_encountered result_determined result_inconclusive)
       else if (Util.string_starts_with_string line "(error ") then
	 (debug_msg ("Z3: "^line); None)
       else (failwith ("Unknown Z3 message: "^line^".\n"); None)
     with End_of_file ->
       ((if result_inconclusive then debug_msg "Z3 has shown contradicting output.\n");
	if unsupported_encountered || (not result_determined) || result_inconclusive then None
	else sofar_result))
  in scan None false false false false
  
(* The options for calling Z3. *)
let z3_opts () : options_t = 
  map_of_list [("TimeOut",       (string_of_int !CmdLine.timeout));
	       ("KeepRtrancl",   "no");
	       ("KeepPointstos", "no")]

(** [z3_prove suppress_errs env sq opts]
    tries to prove a sequent sq with Z3 using options opts, where env gives the types of some of free variables of sq.
    The errors are suppressed iff suppress_errs is true.
    Returns
    - Some true, if the sequent is valid,
    - Some false, if the sequent if is invalid,
    - None, if nothing could be shown about the sequent. *)
let z3_prove (suppress_errs : bool) (env:typeEnv) ((assumptions,succedent) : sequent) (options : options_t) : bool option =
  let s = ((List.map FormUtil.remove_comments antecedent), (FormUtil.remove_comments succedent)) in
  let options = merge_opts (z3_opts ()) options in
  try
    let (env,new_assumptions,new_succedent) = (translate_sequent_to_AUFLIA options (LargeFormUtils.typeEnv2mapVarType env) s) in
    (* Here inlining invoke_z3 options s env new_assumptions new_succedent suppress_errs *)
    let timeout = StringMap.find "TimeOut" options in
    let smt_str = convert_to_smt2_string env new_assumptions new_succedent in
    let in_read, in_write = Unix.pipe () in
    let out_read, out_write = Unix.pipe () in
    let outfile = Unix.in_channel_of_descr in_read in
    let infile = Unix.out_channel_of_descr out_write in
    let clean_child () = Unix.close out_write; Unix.close in_read in 
    let clean_parent () = Unix.close out_read; Unix.close in_write in
    let args = if !Util.verbose then [|"z3";"-smt2";"-in"|] else [|"z3";"-smt2";"-in";"-nw"|] in
    let pid = UnixUtil.create_process_with_pgid "z3" args clean_child clean_parent out_read in_write in_write in
    let neg_pid = (- pid) in
    (* let _ = debug_msg ("Z3 process identifier is "^(string_of_int pid^".\n")) in *)
    let kill_z3 () =
      Unix.kill neg_pid Sys.sigkill; (* The negative number means killing the whole process group of Z3. *) 
      ignore (Unix.waitpid [] neg_pid);
      None
    in
    let exec_z3 () =
      try 
	output_string infile smt_str;
	flush infile;
	close_out infile;
	ignore (Unix.waitpid [] pid);
	check_z3_results outfile
      with Failure x -> kill_z3 ()
    in
    let res_of_eval = Util.eval_with_timeout exec_z3 kill_z3 () timeout in
    let _ = close_out infile; close_in outfile in
    (match res_of_eval with
	Some true -> None (* During translation to SMT some approximations might have happened. Satisfiability of the sequent means nothing. *)
      | Some false -> Some true (* If a formula is unsatisfiable, the original sequent is valid. *)
      | None -> None)
  with Failure x -> Util.warn x; None
