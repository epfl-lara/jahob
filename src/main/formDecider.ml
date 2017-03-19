(** read {!Form} formulas in the given files and try to decide them. *)

open Printf ;;
open Form ;;
open FormUtil ;;


let do_it (filename:string) = 
  let string_f = Util.string_of_file filename in
  let lines = Str.split (Str.regexp_string "\n") string_f in
  let lines' = match lines with
    | "e"::_::tail
    | "vampire"::_::tail
    | "spass"::_::tail
    | tail -> tail
  in
  let string_f = String.concat "\n" lines' in
  let f : form = ParseForm.parse_formula string_f in
  let res : bool = Decider.valid f in
    
    match res with
      | false -> printf "input formula (%s) is NOT valid. Insert coin and try again...\n" filename; exit 1
      | true -> printf "input formula (%s) is VALID. Yahoooo !\n" filename ;;
	  

printf "Begining proof process...\n" ;;

CmdLine.process ();;

Decider.start "pouet";;
ListLabels.iter ~f:do_it !CmdLine.javaFiles;;
Decider.stop false;;
exit 0;;
