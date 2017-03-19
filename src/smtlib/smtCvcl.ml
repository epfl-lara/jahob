(* Dispatch formulas to CVC Lite *)

open Form
open FormUtil
open Common
open SmtPrint
open SmtTranslate
open PrintForm (* For debugging only *)

(* This is a shorthand for printing debug messages for this module. *)
let debug_id : int = Debug.register_debug_module "SmtCvcl"
let debug_msg : (string -> unit) = Debug.debug_msg debug_id
let debug_is_on () : bool = Debug.debug_is_on debug_id

let default_opts () : options_t = 
  let smtPrint_defaults = [("TimeOut",       string_of_int !CmdLine.timeout);
			   ("MaxQuantInst",  "900");
			   ("TryHeuristics", "yes");
			   ("KeepRtrancl",   "no");
			   ("KeepPointstos", "no")] in
    map_of_list smtPrint_defaults

let heuristics_opts : options_t = 
  let smtPrint_defaults = [("TimeOut",       "20");
			   ("MaxQuantInst",  "900");
			   ("TryHeuristics", "yes");
			   ("KeepRtrancl",   "no");
			   ("KeepPointstos", "no");
			  ] in
    map_of_list smtPrint_defaults

let getOption (option_name : string) (options : options_t) : string = 
  StringMap.find option_name options

let cvcl_command suppress_errs o (in_fn : string) (out_fn : string) : string = 
  let timeout = getOption "TimeOut" o in
  let max_quant_inst = getOption "MaxQuantInst" o in
  let transclose = if flag_positive o "KeepRtrancl" then "+trans-closure " else "" in
  let command = 
  ("cvcl " ^ transclose ^ 
   (if false && suppress_errs then " +quiet" else "") ^
   " -max-quant-inst " ^ max_quant_inst ^ 
(*   " -quant-new -quant-lazy" ^ *)
   " -timeout " ^ timeout ^ 
   " -lang smtlib " ^ in_fn ^ 
   (if suppress_errs then " 2>/dev/null" else "") ^
   " > " ^ out_fn) in
    debug_msg (command ^ "\n"); 
    command

let infile_counter = (ref 0 : int ref)
let incr_infile () =
    infile_counter := !infile_counter + 1
let incr_infile_if_debug () =
  if (debug_is_on ()) then (incr_infile ())
let next_infile () : string = 
  "vc" ^ (string_of_int !infile_counter) ^ ".smt"

let outfile_counter = (ref 0 : int ref)
let incr_outfile () =
    outfile_counter := !outfile_counter + 1
let next_outfile () : string =
  "cvcl" ^ (string_of_int !outfile_counter) ^ ".out"

type cvcl_result = Proved | NotProved | TooManyQuantifiers

let check_cvcl_results fn outfile : cvcl_result =
  try
    let line = input_line outfile in
    let _ = close_in outfile in
    let valid_regexp = Str.regexp "Valid" in
    let unsat_regexp = Str.regexp "\\(Unsatisfiable\\)\\|\\(unsat\\)" in
    let invalid_regexp = Str.regexp "Not Valid" in
    let sat_regexp = Str.regexp "\\(Satisfiable\\)\\|\\(sat\\)" in
    let unknown_regexp = Str.regexp "Unknown" in
    if ((Str.string_match valid_regexp line 0) || 
    (Str.string_match unsat_regexp line 0)) then
      (debug_msg "Proved by cvcl.\n"; Proved)
    else
      (if (Str.string_match unknown_regexp line 0) then
	(debug_msg "There may be too many quantifiers.\n"; 
	 TooManyQuantifiers)
      else
	(if ((Str.string_match invalid_regexp line 0) ||
	(Str.string_match sat_regexp line 0)) then
	  debug_msg ("Disproved by cvcl.\n")
	else
	  debug_msg ("cvcl error.\n");
	 debug_msg ("Please see " ^ fn ^ " for complete output.\n");
	 NotProved))
  with End_of_file -> NotProved

let report_timeout (name : string) (o : options_t) : unit =
  Util.msg ("Failed to prove using " ^ name ^ " within the given timeout of " ^
	      (getOption "TimeOut" o) ^
	      "s.\nUse \'-timeout <seconds>\' to increase timeout.\n")

(* The suppress_errs flag was added for the -bohne option, which uses
   cvcl to prove loop invariants. We may want to specialize this
   further using a callback function for error messages, but for now,
   this will avoid the whole problem of the timeout errors that get
   spit out. *)
let invoke_cvcl (o : options_t)
    (s : sequent) (env : typeEnv) (fs : form list) (f : form) (suppress_errs : bool) : cvcl_result =
  let in_fn = (next_infile ()) in
  let fq_in_fn = Util.tmp_name in_fn in
  let fq_out_fn = Util.tmp_name (next_outfile ()) in
  let infile = open_out fq_in_fn in
  let smt_str = (convert_to_smt_string s in_fn env fs f) in
    output_string infile smt_str;
    close_out infile;
    try
      debug_msg ("Invoking cvcl on " ^ in_fn ^ ".\n");
      let exit_code = Util.run_command (cvcl_command suppress_errs o fq_in_fn fq_out_fn) in
	if (exit_code = 0) then
	  let outfile = open_in fq_out_fn in
	  (check_cvcl_results fq_out_fn outfile)
	else if suppress_errs then
	  NotProved
	else ((report_timeout "cvcl" o); NotProved)
    with Failure x -> Util.warn x; NotProved

let invoke_z3 (o : options_t)
    (s : sequent) (env : typeEnv) (fs : form list) (f : form) (suppress_errs : bool) : cvcl_result =
  let _= debug_msg ("invoke_z3 started on sequent\n"^(string_of_sequent s)^"\nwith type environment\n"^(string_of_env env)^"\nand formula list\n["^(wr_form_list ";\n" fs)^"]\nand formula\n"^(string_of_form f)^".\n") in
  let timeout = float_of_string (getOption "TimeOut" o) in  
  let smt_str = (convert_to_smt_string s "jahob" env fs f) in
  let in_read, in_write = Unix.pipe () in
  let out_read, out_write = Unix.pipe () in
  let outfile, infile = Unix.in_channel_of_descr in_read, Unix.out_channel_of_descr out_write in
  let clean_child () = Unix.close out_write; Unix.close in_read in 
  let clean_parent () = Unix.close out_read; Unix.close in_write in
  let pid = 
    let options = if !Util.verbose then [|"z3";"-in";"-nw"|] else [|"z3";"-in"; "-nw"|] in
    UnixUtil.create_process_with_pgid "z3" options  clean_child clean_parent out_read in_write Unix.stderr 
  in
  let kill_z3 () = 
    Unix.kill (- pid) Sys.sigkill; 
    ignore (Unix.waitpid [] (- pid));
    NotProved 
  in
  let exec_z3 () = 
    try      
      output_string infile smt_str;
      flush infile;
      close_out infile;
      ignore (Unix.waitpid [] pid);
      let res = check_cvcl_results "" outfile in
      res
    with Failure x -> kill_z3 ()
  in
  let res = Util.eval_with_timeout exec_z3 kill_z3 () timeout in
  let _ = close_out infile; close_in outfile in
  res


let rec try_one_quantified_form (s : sequent) (env : typeEnv) (nqfs : form list) 
    (totry : form list) (f : form) (suppress_errs : bool) (o : options_t) : bool option =
  match totry with
    | [] -> None
    | next :: rest ->
	let result = invoke_cvcl o s env (next :: nqfs) f suppress_errs in
	  match result with
	    | Proved -> Some true
	    | NotProved | TooManyQuantifiers ->
		(try_one_quantified_form s env nqfs rest f suppress_errs o)

let rec try_fewer_quantifiers (s : sequent) (env : typeEnv) (nqfs : form list) 
    (qfs0 : form list) (qfs1 : form list) (f : form) (suppress_errs : bool) 
    (o : options_t) : bool option =
  match qfs0 with
    | [] -> None
    | next :: qfs -> 
	let result = invoke_cvcl o s env (nqfs @ qfs) f suppress_errs in
	  match result with
	    | Proved -> Some true
	    | NotProved | TooManyQuantifiers ->
		(try_fewer_quantifiers s env nqfs qfs (next :: qfs1) f suppress_errs o)


let try_heuristics (s : sequent) (env : typeEnv) (assumptions : form list) (goal : form) 
    (suppress_errs : bool) (o : options_t) : bool option =
  let is_quantified (f : form) : bool =
    match f with
      | Binder(Forall, _, _)
      | Binder(Exists, _, _) -> true
      | _ -> false in
  let (qfs, nqfs) = List.partition is_quantified assumptions in
  let res = try_fewer_quantifiers s env nqfs qfs [] goal suppress_errs o in
  if Util.safe_unsome false res then res else
  try_one_quantified_form s env nqfs qfs goal suppress_errs o

let cvcl_prove (suppress_errs : bool) (s1 : sequent) (options : options_t) : bool option =
  let s = (List.map remove_comments (fst s1), remove_comments (snd s1)) in
  let options = merge_opts (default_opts ()) options in
  try
    let (env, fs, f) = (process_sequent options s) in
    let result = invoke_cvcl options s env fs f suppress_errs in
      match result with
	| Proved -> incr_infile_if_debug (); Some true
	| NotProved -> incr_infile (); None
	| TooManyQuantifiers -> incr_infile ();
	    if flag_positive options "TryHeuristics" then
	      (try_heuristics s env fs f suppress_errs heuristics_opts)
	    else None
  with Failure x -> incr_infile (); Util.warn x; None

let z3_prove (suppress_errs : bool) (s1 : sequent) (options : options_t) : bool option =
  (* let _ = debug_msg ("z3_prove started on\n"^(string_of_sequent s1)^".\n") in *)
  let s = (List.map remove_comments (fst s1), remove_comments (snd s1)) in
  let options = merge_opts (default_opts ()) options in
  try
    let (env, fs, f) = (process_sequent options s) in
    let result = invoke_z3 options s env fs f suppress_errs in
      match result with
	| Proved ->  incr_infile_if_debug (); Some true
	| _ -> incr_infile (); None
  with Failure x -> Util.warn x; None
