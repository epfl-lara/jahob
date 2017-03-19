(** read one {!Form} formula in the given file and try to decide it with the minimal
    posible set of assumptions, while preserving the order in which assumptions are given.
 *)

open Printf ;;
open Form ;;
open FormUtil ;;
open Common


let last_time = ref 0.0

let merged = ref ""

let try_with_limited_assumptions ((hyps, goal):sequent) (n:int) =
  CmdLine.usedps := [];
  
  let ratio = n * 100 / (List.length hyps) in

    CmdLine.add_usedp (!merged ^ sprintf ":Filter=%d" ratio);
  
    let start = Unix.gettimeofday () in
    let f = form_of_sequent (n_first n hyps, goal) in
      printf "trying with %d : \n" n;
      let r = Decider.valid f in
	if r then last_time := Unix.gettimeofday () -. start;
	r


(* invariants : it works with max assumptions, and not with min *)
let rec search min max s : int = 
  if min = max - 1 then max
  else
    let n = min + (max - min) / 2 in
      if try_with_limited_assumptions s n then 
	search min n s
      else
	search n max s
	  

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
    merged := (if options_string = "" then prover else prover ^ ":" ^ options_string);

      merged := !merged ^ ":Sorting";
      
(*    print_string merged; *)

  let (hyps, goal) = sequent_of_form f in
  let n = (List.length hyps) in

    CmdLine.add_usedp (!merged);

  let start = Unix.gettimeofday () in
  let r = Decider.valid f in
  let full_time = Unix.gettimeofday () -. start in

    if not r then fprintf stderr "ERROR : could not prove %s with the provided parameters....\n" filename;

  let min_needed = search 0 n (List.rev hyps, goal) in
    fprintf stderr "%s ; %d ; %d ; %f ; %f\n" filename min_needed n !last_time full_time;;

CmdLine.process ();;

Decider.start "pouet";;

ListLabels.iter ~f:do_it !CmdLine.javaFiles;;

Decider.stop ();;
