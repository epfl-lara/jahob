(** Lemma caching for {!Isabelle} module.
    Enables reading previously proved lemmas from files.
    Implements some lemma matching that allows using
    stronger lemmas to prove weaker ones. *)

open Form

let known_facts = ref ([] : (string * form) list)
let add_fact s = 
  known_facts := s :: !known_facts

let get_content fname =
  if Sys.file_exists fname then
    let chn = open_in fname in
    let len = in_channel_length chn in
    let str = String.make len ' ' in
    let _ = really_input chn str 0 len in
    (close_in chn; str)
  else
    (Util.msg ("No lemma file " ^ fname);
    "")

let remove_comments (s : string) : string =
  let begin_comment = Str.regexp "(\\*" in
  let end_comment = Str.regexp "\\*)" in
  let rec remove (s : string) (pos : int) : string =
    try
      let begin_pos = Str.search_forward begin_comment s pos in
      let end_pos = Str.search_forward end_comment s (pos + 2) in
      let head = Str.string_before s begin_pos in
      let tail = Str.string_after s (end_pos + 2) in
	remove (head ^ " " ^ tail) begin_pos
    with Not_found -> s
  in
    remove s 0

let init mod_name : unit = 
  let lemma_file_name = mod_name ^ "-lemmas" ^ ".thy" in
  let _ =  Util.msg ("opening lemma file : " ^ lemma_file_name ^ "\n") in
  let str = remove_comments (get_content lemma_file_name) in
  let ws = "[ \t\r\n]+" in     (* one or more whitespace characters *)
  let opt_ws = "[ \t\r\n]*" in (* zero or more whitespace characters *)
  let opt_name = "\\(" ^ ws ^ "[a-zA-Z0-9_]+" ^ opt_ws ^ ":\\)?" in
  let formula = "\\([^\"]*\\)" in
  let format_regexp = Str.regexp ("lemma" ^ opt_name ^ opt_ws ^ "\"" ^ formula ^ "\"") in
  let pos = ref 0 in
  let rec get_next_lemma () : unit =
    try 
      let _ = Str.search_forward format_regexp str !pos in
      let _ = pos := Str.match_end () in
      let s1 = Str.matched_group 2 str in
	add_fact (s1, ParseForm.parse_formula s1);
	get_next_lemma ()
    with Not_found -> ()
  in 
    get_next_lemma ();
    (* List.iter (fun s -> print_string (s ^ "\n\n")) !known_facts; *)
    Util.msg (Printf.sprintf "Retrieved %d lemmas from lemma file %s.\n" (List.length !known_facts) lemma_file_name)
      
let buzzneq (f,g) =
  (Debug.msg "\nNOTE:\n";
   Debug.msg (PrintForm.string_of_form f);
   Debug.msg "\n    APPARENTLY NOT SAME AS:    \n";
   Debug.msg (PrintForm.string_of_form g ^ "\n");
   false)

let rec same f g = match (f,g) with
| (App(Const Comment, [Const (StringConst c);f1]),g) -> same f1 g
| (f, App(Const Comment, [Const (StringConst c);g1])) -> same f g1
| (TypedForm(f1,t1),g) -> same f1 g
| (f,TypedForm(g1,t1)) -> same f g1
| (_,_) when impl f g && impl g f -> true
| (App(Const Eq,[f1;f2]),App(Const Eq,[g1;g2])) ->
    (same f1 g1 && same f2 g2) ||
    (same f1 g2 && same f2 g1)
| (App(f1,fs),App(g1,gs)) -> same f1 g1 && same_all fs gs
| (Binder(bf,_,f1),Binder(bg,_,g1)) when bf=bg -> same f1 g1
| (f1,g1) when f1=g1 -> true
| _ -> buzzneq(f,g)
and same_all fs gs = match (fs,gs) with
| ([],[]) -> true
| (f1::fs1,g1::gs1) -> same f1 g1 && same_all fs1 gs1
| _ -> false
and impl f g = begin
match (f,g) with
| (App(Const MetaImpl,[f1;f2]),App(Const MetaImpl,[g1;g2])) ->
   impl f2 g2 && impl g1 f1
| (f,App(Const MetaImpl,[g1;g2])) -> impl f g2
| (f,App(Const MetaAnd,gs)) -> List.for_all (impl f) gs
| (f,App(Const And,gs)) -> List.for_all (impl f) gs
| (App(Const Or,fs),g) -> List.for_all (fun f0 -> impl f0 g) fs
| (App(Const MetaAnd,fs),g) -> List.exists (fun f0 -> impl f0 g) fs 
| (App(Const And,fs),g) -> List.exists (fun f0 -> impl f0 g) fs 
| (f,App(Const Or,gs)) -> List.exists (impl f) gs
| (App(Const Comment, [Const (StringConst c);f1]),g) -> impl f1 g
| (f, App(Const Comment, [Const (StringConst c);g1])) -> impl f g1
| (TypedForm(f1,t1),g) -> impl f1 g
| (f,TypedForm(g1,t1)) -> impl f g1
| (Binder(bf,_,f1),Binder(bg,_,g1)) when bf=bg -> impl f1 g1
      (* all binders assumed monotonic, although lambda is not used *)
| (App(Const Eq,[f1;f2]),App(Const Eq,[g1;g2])) ->
    (same f1 g1 && same f2 g2) ||
    (same f1 g2 && same f2 g1)
| (App(f1,fs),App(g1,gs)) -> same f1 g1 && same_all fs gs
| (f1,g1) when f1=g1 -> true
| (_,_) -> buzzneq(f,g)
end

(* Checks that two formulas are the same modulo skolem constants as
   follows:
   1. Sorts the assumptions by structure.
   2. Renames bound variables and remove types.
   3. Renames free variables.
   4. Removes types in bound variables.
*)
let equal_mod_skolem_variables (f0 : form) (f1 : form) : bool =
  let ids0 = 
    Util.union (FormUtil.ids_in_use f0) (FormUtil.ids_in_use f1) in
  let f0' = FormUtil.normalize_for_matching f0 ids0 in
  let f1' = FormUtil.normalize_for_matching f1 ids0 in
    FormUtil.equal f0' f1'

let implied (lemma_str, lemma) (assumption_str, assumption) = 
  begin
(*
  Util.msg "VERIFYING IMPLICATION:\n";
  Util.msg ("\"" ^ assumption_str ^ "\"\n");
  Util.msg "    ==>?    \n";  
  Util.msg ("\"" ^ lemma_str ^ "\"\n");
*)
    let res_sem = impl assumption lemma in
(*
    let _ = if res_sem then Util.msg "YES, implied!\n\n"
                       else Util.msg "NO, NOT implied!\n" in
*)
    let res_syn = (lemma_str = assumption_str) in
(*
    let _ = if res_syn then Util.msg "SYNTACTICALLY IDENTICAL.\n\n"
                       else Util.msg "SYNTACTICALLY NOT IDENTICAL.\n\n" in
    let _ = if res_syn && (not res_sem) then 
               Util.msg "ALAS, SEMANTIC LOSES TO SYNTAX!\n" 
            else () in
*)
    let res_sko () : bool = equal_mod_skolem_variables lemma assumption in
    (res_syn || res_sem || res_sko ())
  end  

let known_fact ((lemma_str,lemma) : string * form) : bool = 
  try
    let (cached_str, _) = 
      List.find (implied (lemma_str,lemma)) !known_facts in
    Util.msg ("\nMatched known lemma:\n" ^ cached_str ^ "\n\n");
    true
  with Not_found ->
    false
