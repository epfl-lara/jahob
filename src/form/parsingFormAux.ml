(** Auxiliary file used to avoid module recursion,
   stores error handling routing for the generated {!Form} formula parser. *)

type bufp = Lexing.lexbuf option ref 

let (input : string option ref) = ref None
let (buffer : bufp) = ref None

let marker = " <*> "

let parse_error s = match !input with
| Some inp -> (match !buffer with
  | Some buf ->
      let pos = buf.Lexing.lex_curr_p.Lexing.pos_cnum in
      let init = String.sub inp 0 pos in
      let rest = String.sub inp pos (String.length inp - pos) in
      print_string ("Parse error:\n" ^ init ^ marker ^ rest ^ "\n")
  | _ -> print_string ("Parse error in uninitialized parse state."))
| _ -> print_string ("Parse error in uninitialized parse state.")
