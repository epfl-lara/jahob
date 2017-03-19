(** Utility module with miscellaneous functions,
    including string functions and operating system functions.

  TODO: Sort functions by category, clean up.
 *)

exception Bad_string
exception Bail

(** Qualify helper file name *)
(* if you want to install the executable in one directory (e.g. /usr/bin),
 * but put helper files in another (/usr/share/module-language),
 * here's what you need to change! *)
let qualify_helper_fn n =
  let d =  Filename.dirname Sys.executable_name ^ "/" in
  (* Sys.getcwd() ^ "/" ^ *) d ^ n

(** Find the library directory given its path. Try from '../lib/'
    before from '/'.*)
let lib_name n =
  try (let d = Filename.dirname Sys.executable_name ^ "/../lib/" in
	 (* Sys.getcwd() ^ "/" ^ *) d ^ n)
  with Sys_error _ -> n

(** Same as [lib_name] for temporary directory. *)
let jahob_tmp_name n =
  try (let d = Filename.dirname Sys.executable_name ^ "/../tmp/" in    
	 (* Sys.getcwd() ^ "/" ^ *) d ^ n)
  with Sys_error _ -> n

let tmp_name n =
  try Filename.temp_file n ""
  with Sys_error _ -> n


(** filename handling; returns the inverse of Filename.chop_extension *)
let extension n =
  let d = String.rindex n '.' in
  String.sub n d (String.length n - d)

(** Return the directory path of a file. *)
let get_path s = 
  if String.contains s '/' then
    let i = String.rindex s '/' in
    String.sub s 0 (i+1)
  else ""


(** {6 List-handling stuff} *)


(** Same as [List.remove_assoc] but raise Not_found if no pair is found. *)
let rec must_remove ident = function
  | [] -> raise Not_found
  | ((id, v) as t) :: q -> if id = ident then q else t :: (must_remove ident q)

let rec remove_dups = function
  |  [] -> []
  | q::qs -> if (List.mem q qs) then remove_dups qs else q::(remove_dups qs)

(** [remove_dups_assoc] removes all duplicates by testing equality on the
    first component: only the first occurence is kept. *)
let rec remove_dups_assoc = function
  | [] -> []
  | (a, b) as t :: q -> t :: 
      remove_dups_assoc (List.filter (fun x -> fst x <> a) q)

let rec find_dups = function
  | [] -> []
  | q::qs -> if (List.mem q qs) then q::(find_dups qs) else find_dups qs

let disjoint l1 l2 = 
  List.for_all (fun x -> not (List.mem x l2)) l1

let intersect l1 l2 =
  List.filter (fun x -> List.mem x l2) l1

let difference l1 l2 =
  List.filter (fun x -> not (List.mem x l2)) l1

let union l1 l2 =
  difference l1 l2 @ l2 

let set_remove elem lst =
  let rec remove_rec lst1 lst2 =
    match lst1 with
      | elem0 :: lst1' ->
	  if (elem = elem0) then 
	    (List.rev lst2) @ lst1'
	  else remove_rec lst1' (elem0 :: lst2)
      | [] -> List.rev lst2 in
    remove_rec lst []

let set_add elem lst =
  if (List.mem elem lst) then lst else (elem :: lst)

let rec list_last = function
  | [] -> None
  | [x] -> Some x
  | x::xs1 -> list_last xs1

(** Extract the last element of the list. Raise
    [invalid_arg "Util.firsts_last"] if the list is empty. *)
let rec firsts_last xs =
  match List.rev xs with
    | [] -> invalid_arg "Util.firsts_last"
    | x :: xs1 -> (x, List.rev xs1)

(** Composition of [List.map] and [List.partition] *)
let partition_map p f xs =
  List.fold_right (fun x (ys, zs) -> if p x then (f x :: ys, zs) 
      else (ys, f x :: zs)) xs ([], [])

(** Composition of [List.map] and [List.filter] *)
let filter_map p f xs =
  List.fold_right (fun x ys -> if p x then f x :: ys else ys) xs []

(** Find an element in a list and apply a function on that element *)  
let rec find_map (f : 'a -> 'b option) (xs : 'a list) : 'b =
  match xs with
  | x::xs' -> 
      (match f x with
      |	None -> find_map f xs'
      | Some y -> y)
  | [] -> raise Not_found

(** [map_fst f l] maps [f] on the first component of the elements of [l]. *)
let rec map_fst f = function
  | [] -> []
  | (x, y) :: q -> (f x, y) :: map_fst f q

(** [map_snd f l] maps [f] on the second component of the elements of [l]. *)
let rec map_snd f = function
  | [] -> []
  | (x, y) :: q -> (x, f y) :: map_snd f q

(** [map_couple f l] maps [f] on both components of the elements of [l]. *)
let rec map_couple f = function
  | [] -> []
  | (x, y) :: q -> (f x, f y) :: map_couple f q

(** Combination of List.assoc and List.remove *)
let assoc_remove key assoc_list =
  let rec ar acc = function
    | [] -> raise Not_found
    | (key', v) :: assoc_list' when key = key' -> 
	(v, List.rev_append acc assoc_list') 
    | kv :: assoc_list' -> ar (kv :: acc) assoc_list'
  in ar [] assoc_list

(** Replace association [(key, v)] with
   [(key, fn v)] in association list [assoc_list]. If no association with 
   [key] exists then add [(key, default)] to the list. *)
let assoc_replace key fn default assoc_list =
  let rec ar acc = function
    | (key', v)::assoc_list' when key = key' ->
	(key, fn v)::List.rev_append acc assoc_list'
    | (key', v)::assoc_list' -> ar ((key', v)::acc) assoc_list'
    | [] -> (key, default)::List.rev acc
  in ar [] assoc_list

(** Split the list of length k>=1 into a pair consisting of
   the list of first k-1 elements and the last element. *)
let rec firsts_last xs = match xs with
| [] -> failwith "Util.first_lasts: empty list"
| [x] -> ([],x)
| x::xs1 ->
    let (fs,l) = firsts_last xs1 in
    (x::fs,l)

(** Split a list of length n > k into a pair consisting of the first k
    elements and the last (n - k) elements. *)
let unappend (b : 'a list) (k : int) : ('a list * 'a list) =
  let rec unappend_rec (a : 'a list) (b : 'b list) : ('a list * 'a list) =
    if (List.length a = k) then (a, b)
    else match b with
      | [] -> failwith "Util.unappend: list not long enough"
      | x :: xs -> unappend_rec (a @ [x]) xs in
    unappend_rec [] b
    
(** generate a list of length [n] using generator [f] *)
let generate_list (f : int -> 'a) (n : int) : 'a list = 
  let rec mk_tl n acc = 
    if n <= 0 then acc 
    else mk_tl (n - 1) (f n :: acc) 
  in mk_tl n []

(** Exchange the position of the components in a couple list. *)
let rec swap = function
  | [] -> []
  | (a, b) :: q -> (b,a) :: (swap q)


(** {6 String-handling utility functions} *)


let trim_quotes s = 
  let trim_last s' = if String.get s' ((String.length s')-1) = '"' then
    String.sub s' 0 ((String.length s')-1) else s' in
  if String.get s 0 = '"' then 
    (trim_last (String.sub s 1 ((String.length s) - 1)))
  else
    trim_last s

let unescaped s =
  let n = ref 0 in
    for i = 0 to String.length s - 1 do
      n := !n +
        (match String.unsafe_get s i with
           '\\' when String.unsafe_get s (i+1) != '\\' ->
             (match String.unsafe_get s (i+1) with
               'n' -> 0
             | 't' -> 0
             | _ -> 1)
        | _ -> 1)
    done;
    if !n = String.length s then s else begin
      let s' = String.create !n in
      n := 0;
      let skip = ref 0 in
      (try (for i = 0 to String.length s - 1 do
        begin
          if (i + !skip) = String.length s then raise Bail;
          match String.unsafe_get s (i + !skip) with
          | '\\' when String.unsafe_get s (i+ !skip+1) != '\\' ->
              (match String.unsafe_get s (i+ !skip+1) with
                'n' -> String.unsafe_set s' !n '\n'; incr skip
              | 'r' -> String.unsafe_set s' !n '\r'; incr skip
              | 't' -> String.unsafe_set s' !n '\t'; incr skip
              | '\\' -> String.unsafe_set s' !n '\\'; incr skip;
              | _ -> raise Bad_string)
          | c -> String.unsafe_set s' !n c
        end;
        incr n
      done) with Bail -> ());
      Str.first_chars s' (String.length s - !skip)
    end


(** {6 namespace mangling stuff} *)

(* split_by: string -> string -> (string list) i
   splits the second argument into substrings, taking as delimiters the first argument, and returns the list of substrings. For instance, split "." s splits s into words which were separated by dots. An occurrence of the delimiter at the beginning and at the end of the string is ignored.
*)
let split_by sep =
  Str.split (Str.regexp_string sep) 
(* Previous version was more complicated and slightly less efficient:
let split_by sep s =
  let sep_regexp = Str.regexp (Str.quote sep) in
    Str.split sep_regexp s
*)

let substring (small : string) (big : string) : bool =
  let re = Str.regexp (Str.quote small) in
    try (let _ = Str.search_forward re big 0 in true)
    with Not_found -> false

let qualify mname n =
  if mname = "" then n else (mname ^ "." ^ n)

let qualify_if_needed mname n =
  if mname = "" || String.contains n '.' then n else (mname ^ "." ^ n)

(** return the class name, if any *)
let unqualify_getting_module s =
  if String.contains s '.'
  then String.sub s 0 (String.rindex s '.')
  else ""

let unqualify s =
  if String.contains s '.' then
    let i = String.rindex s '.' in
    String.sub s (i+1) (String.length s - i - 1)
  else s

(** [unqualify class name] is the same as [unqualify name], but trims only
    the class name [class]. *)
let unqualify1 class_name =
  let prefix = class_name ^ "." in
  let size = String.length prefix in
    fun s ->
      if String.length s > size && String.sub s 0 size = prefix
      then String.sub s size (String.length s - size)
      else s

(** Separate a qualified name into its two components. *)
let unqualify2 s = 
  match split_by "." s with
    | [mod_name; proc_name] -> (mod_name, proc_name)
    | _ -> failwith ("Invalid qualified name " ^ s)

let unprime s =
  let l = String.length s in 
    if l = 0 then s else 
      if (String.get s (l-1)) = '\'' then
        String.sub s 0 (l-1) else s

let is_primed s =
  let l = String.length s in 
    if l = 0 then false else 
      (String.get s (l-1) = '\'')

let replace_dot_with_uscore s =
  let dot = Str.regexp "\\." in
  let caret = Str.regexp "\\^" in
    Str.global_replace dot "_" 
      (Str.global_replace caret "$" s)

(** Error-handling functions. *)

let error_list = ref []
let no_errors () = (List.length !error_list = 0)

let err loc msg = 
  error_list := !error_list @
    [loc ^ ": error: "^msg]

let error msg = (print_string (msg ^"\n"); flush_all(); err "" msg)
(*
let print_errors () = 
  List.iter (function x -> print_string (x ^ "\n")) !error_list;
  print_string (string_of_int (List.length !error_list)^" errors.\n");
  print_string "The program is INVALID\n";
  exit 2
*)

(** Printing notifications [msg, amsg, etc] *)
let verbose = ref false

(** always print this message *)
let amsg s = print_string s; flush_all ()

(** print only if -v *)
let msg s = if !verbose then amsg s

let (warning_no : int ref) = ref 0
let warn msg = 
  incr warning_no;
  print_string ("*** Warning: "^ msg ^ "\n"); flush_all()

let fail s =   
  print_string (s ^ "\n"); 
  Printf.printf "There were %d warnings.\n" !warning_no;
  flush_all();
  failwith s

let warn_if_none ov msg = match ov with
  | None -> warn msg
  | Some _ -> ()

(** Failing on warnings *)

let resilient = ref false
let fail_if_warned (s : string) : unit =
  if (!warning_no > 0) then
    (print_string(" *** " ^ s ^ "\n");
     (if !resilient then 
	(msg("       -resilient option used, so Jahob is continuing \
                      despite warnings");
	 (warning_no := 0))
      else fail "     Jahob failed due to warnings in this phase; \
                      use -resilient option to ignore them"))
  else ()
  
(** removing 'option' types *)
let unsome : 'a option -> 'a = 
function
  | Some x -> x
  | None   -> failwith "[util] tried to deoptionify None"

let safe_unsome default : 'a option -> 'a = 
function
  | Some x -> x
  | None -> default

(** Apply a function to the element under the option constructor, if any. *)
let some_apply f = function
  | None -> None
  | Some x -> Some (f x)

(** Apply a function to the element under the option constructor, if any. *)
let unsome_apply default f = function
  | None -> default
  | Some x -> f x

(** Apply the function on the default value and the content of the option
    constructor if any, otherwise return the default value. *)
let some_fold f acc = function
  | None -> acc
  | Some x -> f x acc

(* let optmap = some_apply *) (* DEPRECATED *)

let empty l = match l with [] -> true | _ -> false

(** Read the given file into a string. *)
let string_of_file (fname : string) =
  if Sys.file_exists fname then
    let chn = open_in fname in
    let len = in_channel_length chn in
    let str = String.make len ' ' in
    let _ = really_input chn str 0 len in
    (close_in chn; str)
  else
    (warn ("Could not read file " ^ fname ^ "; assuming empty content.");
     "")

let fileLine (fn:string) : string =
  begin
    let chn = open_in fn in
      let str = input_line chn in
      close_in chn;
      str
  end

(** Use timed_command utility to run an external process with a timeout. *)

(*
let timed_command = qualify_helper_fn "timed_command"
*)
let timed_command = "timeout"

(** Note: these commands may result in compatibility problems because shells on different platforms are different.  
    Check especially the syntax for redirection. *)

let run_command (prog : string) : int =
  Sys.command prog


(** Execute a function with a timeout *)

exception Timeout

let eval_with_timeout =
  let handle_sigalrm signo = 
    if !verbose then msg "Timeout occurred."; 
    raise Timeout
  in
  let set_timer tsecs =
    ignore (Unix.setitimer Unix.ITIMER_REAL
              { Unix.it_interval = 0.0; Unix.it_value = tsecs })
  in fun f defaultval arg tsecs ->
    let oldsig = Sys.signal Sys.sigalrm (Sys.Signal_handle handle_sigalrm) in
    try
      set_timer tsecs;
      let res = f arg in
      set_timer 0.0;
      Sys.set_signal Sys.sigalrm oldsig;
      res
    with Timeout ->
      Sys.set_signal Sys.sigalrm oldsig;
      defaultval arg

open Unix

(** Run external program with timeout *)
let run_with_timeout (prog : string) (args : string list) 
    (prog_stdin : file_descr) (prog_stdout : file_descr) (prog_stderr : file_descr)
    (seconds : int) : process_status =
  let secs = if seconds <= 0 then 1 else seconds in
  let tsecs = float_of_int secs in
  let clean () = () in
  let pid = UnixUtil.create_process_with_pgid 
      prog 
      (Array.of_list (prog::args)) 
      clean clean
      prog_stdin prog_stdout prog_stderr 
  in
  eval_with_timeout 
    (fun pid -> snd (Unix.waitpid [] pid))
    (fun pid -> 
      kill (- pid) Sys.sigkill; 
      snd (Unix.waitpid [] (- pid))) 
    pid tsecs 

let run_with_timeout_redirect_out (prog : string) (args : string list) 
    (seconds : int) (silent : bool) : (process_status * in_channel) =
  let in_descr, out_descr = pipe () in
  let err_chan = 
    if not silent then Pervasives.stderr else 
    open_out "/dev/null"
  in
  let err_descr = descr_of_out_channel err_chan in   
  let clean_resources () =
    close out_descr;
    if silent then begin
      close_out err_chan
    end
  in
  try
    let res = run_with_timeout prog args stdin out_descr err_descr seconds in
    clean_resources ();
    res, in_channel_of_descr in_descr
  with e -> clean_resources (); close in_descr; raise e

let run_with_timeout_out (prog : string) (args : string list) 
    (outfile : string) (seconds : int) (silent : bool) : process_status =
  let out_chan = open_out outfile in
  let err_chan =  
    if not silent then Pervasives.stderr else 
    open_out "/dev/null"
  in
  let out_descr = descr_of_out_channel out_chan in
  let err_descr = descr_of_out_channel err_chan in   
  let clean_resources () =
    close_out out_chan;
    if silent then begin
      close_out err_chan
    end
  in
  try
    let res = run_with_timeout prog args stdin out_descr err_descr seconds in
    clean_resources ();
    res
  with e -> clean_resources (); raise e

let run_with_timeout_in_out (prog : string) (args : string list) 
    (infile : string) (outfile : string)
    (seconds : int) (silent : bool) : process_status =
  let in_chan = open_in infile in
  let out_chan = open_out outfile in
  let err_chan =  
    if not silent then Pervasives.stderr else 
    open_out "/dev/null"
  in
  let in_descr = descr_of_in_channel in_chan in
  let out_descr = descr_of_out_channel out_chan in
  let err_descr = descr_of_out_channel err_chan in   
  let clean_resources () =
    close_in in_chan;
    close_out out_chan;
    if silent then begin
      close_out err_chan
    end
  in
  try
    let res = run_with_timeout prog args in_descr out_descr err_descr seconds in
    clean_resources ();
    res
  with e -> clean_resources (); raise e
  

let rec fold_right1pair (f : 'a * 'a -> 'a) (xs : 'a list) : 'a =
  match xs with
    | [] -> failwith "Util.fold_right1pair: list empty"
    | [x] -> x
    | x::xs1 -> f (x, (fold_right1pair f xs1))


let measured_time = ref 0.
let measured_calls = ref 0

(** measure accumulated execution time and number of calls to a particular function *)
let measure fn arg =
  let start_time = 
    let ptime = Unix.times () in
    ptime.tms_utime
  in
  try
    let res = fn arg in
    let end_time = 
      let ptime = Unix.times () in
      ptime.Unix.tms_utime
    in
    measured_time := !measured_time +. (end_time -. start_time);
    incr measured_calls;
    res
  with e ->
    let end_time = 
      let ptime = Unix.times () in
      ptime.Unix.tms_utime
    in
    measured_time := !measured_time +. (end_time -. start_time);
    incr measured_calls;
    raise e

(** Create a fresh name for an identifier by appending a unique number to it.
    Each identifier has its own numbering and numbers start at 1 *)
let fresh_name =
  let table = Hashtbl.create 67 in
    fun id -> 
      id ^ "_" ^(string_of_int (
                   try let num = Hashtbl.find table id in
                     Hashtbl.replace table id (num+1); num
                   with Not_found -> Hashtbl.add table id 2; 1))

(** Currify a function. *)
let curry f x y = f (x, y)

(** Uncurrify a function. *)
let uncurry f (x, y) = f x y

(* -------------------------- *)
(* Added by Alexander Malkis. *)
(* Returns true if the input is an alphanumeric character in the intervals A-Z, a-z or 0-9*)
let isalnum_ (c:char) =
  (c='0')||(c='1')||(c='2')||(c='3')||(c='4')||(c='5')||(c='6')||(c='7')||(c='8')||(c='9')||(c='A')||(c='B')||(c='C')||(c='D')||(c='E')||(c='F')||(c='G')||(c='H')||(c='I')||(c='J')||(c='K')||(c='L')||(c='M')||(c='N')||(c='O')||(c='P')||(c='Q')||(c='R')||(c='S')||(c='T')||(c='U')||(c='V')||(c='W')||(c='X')||(c='Y')||(c='Z')||(c='a')||(c='b')||(c='c')||(c='d')||(c='e')||(c='f')||(c='g')||(c='h')||(c='i')||(c='j')||(c='k')||(c='l')||(c='m')||(c='n')||(c='o')||(c='p')||(c='q')||(c='r')||(c='s')||(c='t')||(c='u')||(c='v')||(c='w')||(c='x')||(c='y')||(c='z')||(c='_')

(* Is character a whitespace, a tab, a new line CR or LF *)
let is_white (c:char) =
  (c=' ') || (c='\n') || (c='\r') || (c='\t')

(* is character a left parenthesis of any type *)
let is_left_paren (c:char) =
  (c='(') || (c='{') || (c='[')

(* is character a right parenthesis of any type *)
let is_right_paren (c:char) =
  (c=')') || (c='}') || (c=']')

(* Right-trim a string, removing the trailing blanks, returning the string without the trailing blanks and its last nonblank character if such exists *)
let right_trim (s:string) : (string * (char option)) =
  let rec loop index_preceding_white =
    if (index_preceding_white<0 || not (is_white (s.[index_preceding_white]))) then index_preceding_white
    else loop (index_preceding_white-1)
  in let index_before_whites= loop ((String.length s)-1)
  in if index_before_whites<0 then ("",None) else ((String.sub s 0 (index_before_whites+1)), (Some s.[index_before_whites])) 
    
(* Left-trim a string, removing the initial blanks, returning the string and its leftmost nonblank character if such exists *)
let left_trim (s:string) : (string * (char option)) =
  let len=String.length s in
  let rec loop index_after_white =
    if (index_after_white>=len || not(is_white (s.[index_after_white]))) then index_after_white
    else loop (index_after_white+1)
  in let index_after_whites = loop 0
  in let newlen=len-index_after_whites
  in if newlen=0 then ("",None) else ((String.sub s index_after_whites newlen), (Some s.[index_after_whites]))

(** [string_starts_with_string s1 s2]
    returns true if s1 starts with s2, false otherwise *)
let string_starts_with_string s1 s2 =
  let ln = String.length s2 in
  try (s2 = (String.sub s1 0 ln))
  with Invalid_argument _ -> false

(* --------------------- *)
