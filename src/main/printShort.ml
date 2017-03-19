(** read {!Form} formulas in the given files and print them in condensed form. *)

open Printf 
open Form
open FormUtil 

let print_short_form (filename:string) : unit = 
  let string_f = Util.string_of_file filename in
  let f : form = ParseForm.parse_formula string_f in
  let _ = Util.fail_if_warned "Error parsing formula" in
    print_string (PrintForm.short_string_of_form f);
    print_string "\n\n"
	  
let _ = CmdLine.process ()

let _ = ListLabels.iter ~f:print_short_form !CmdLine.javaFiles

