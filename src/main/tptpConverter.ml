(** read one {!Form} formula in the given file and convert it to the TPTP format *)

open Printf ;;
open Form ;;
open FormUtil ;;
open Common

let load_file (filename:string) = 
  let string_f = Util.string_of_file filename in
  let lines = Str.split (Str.regexp_string "\n") string_f in
    match lines with
      | prover::options::tail -> 
	  let f = String.concat "\n" tail in
	    (prover,options, ParseForm.parse_formula f)
      | _ -> assert false

let do_it (filename:string) = 
  let prover, options_string, f = load_file filename in
  let s = sequent_of_form f in

  let merged = (if options_string = "" then prover else prover ^ ":" ^ options_string) in

    let options = ListLabels.fold_left ~f:CmdLine.split_equal ~init:(StringMap.empty) (Str.split (Str.regexp_string ":") options_string) in

    let chn = open_out (filename ^ ".tptp") in
    let _  = TptpPrettyPrinter.output_sq s options chn in
      close_out chn;
      fprintf stderr "%s -> %s.tptp\n" filename filename;;

CmdLine.process ();;

ListLabels.iter ~f:do_it !CmdLine.javaFiles;;
