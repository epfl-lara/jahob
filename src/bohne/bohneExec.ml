(** jahob main application. *)

let errors = ref 0
let error msg =
  incr errors;
  Printf.eprintf "%s: %s\n" (Source.location ()) msg

let parse() =
  try
    Source.with_lexbuf
      (fun lexbuf ->
	let result = Parser.goal Lexer.token lexbuf in
        (*
	List.iter print_comment result.Syntax.comments;
	Pretty.print Format.std_formatter result;
         *)
        Some result)
  with e -> (error (Printexc.to_string e); None)

let units = ref ([] : Syntax.compilation_unit list)

let rec parse_java_files (files : string list) =  
  match files with 
    | [] -> ()
    | file::files1 -> 
	Source.set_file_name file;
	(match parse() with
	   | None -> Util.warn ("Java file " ^ file ^ " failed to parse.")
	   | Some ast -> units := ast :: !units);
	parse_java_files files1

let std_java_files = 
  if !CmdLine.builtinstd then [] else List.map Util.lib_name ["Object.java"; "Array.java"]

let invoke () : bool =
  parse_java_files (std_java_files @ !CmdLine.javaFiles);
  Debug.msg 
    (Printf.sprintf "Number of compilation units processed: %d.\n"
       (List.length !units));
  Util.fail_if_warned("PARSING FAILED.");
  let _ = (Javajast.number_of_assumes := 0) in
  let (p,task) = Javajast.joust2jast !units (CmdLine.get_task()) in
  let u = Jastjava.jast2joust p in
  Util.fail_if_warned("CONVERSION TO Jast FAILED.");
  let ast = Jast2ast.c_program p in
  Util.fail_if_warned("CONVERSION TO Ast FAILED.");
  let _ = if !CmdLine.sastVC then 
    (let sast = Sast.ast2sast ast in
       if !CmdLine.printSAst then
	 print_string (PrintAst.simplified_program sast))
  in
  (*try *)
    ignore (Analyze.analyze ast task);
    let assume_report = 
      if !Javajast.number_of_assumes = 0 then ""
      else if !Javajast.number_of_assumes = 1 then 
	" (modulo one assume statement)"
      else Printf.sprintf " (modulo %d assume statements)" 
	  !Javajast.number_of_assumes
    in
    if !CmdLine.bohne_refine then
      Util.amsg ("\n0=== Verification SUCCEEDED" ^ assume_report ^ ".\n")
    else 
      Util.amsg ("\n0=== Fixed point reached.\n"); 
    true
(*with BohneRefine.RealCounterexample _ -> 
    Util.amsg "\n-1=== Verification FAILED.\n"; false *)
   
open CmdLine
open Common

let usage_msg =
  ("Usage:\n  " ^ Sys.argv.(0) ^ " [options] <inputJavaFiles> [(-usedp | -excludedp) <IDs>]\n")


let rec cmd_options = 
  [("-v", Arg.Set Util.verbose,
    "Display verbose messages");
   ("-verbose", Arg.Set Util.verbose,
    "Display verbose messages");
   ("-debug", Arg.Set Debug.debugOn,
    "Display debugging messages");
   ("-debuglevel", Arg.Int Debug.set_debug_level,
    "<int> Adjust amount of debug messages, default " ^ Printf.sprintf "%d" !Debug.debug_level);
   ("-debugmodules", Arg.String Debug.set_debug_modules,
    "<modules> Turn on debug messages for a specific module (e.g. SmtPrint)");
   ("-abstractfinal", Arg.Set bohne_abstract_final,
    "Include final transitions in fixed point computation");
   ("-extraprecise", Arg.Set bohne_extra_precise,
    "Use more precise abstraction");
   ("-nosplitting", Arg.Set bohne_no_splitting,
    "Do not split Boolean heaps");
   ("-nobackground", Arg.Clear background,
    "Do not generate verification condition background formula");
   ("-nopreddicovery", Arg.Clear bohne_derive_preds,
    "Do not discover predicates automatically in Bohne");
   ("-norefine", Arg.Clear bohne_refine,
    "Do not use abstraction refinement");
   ("-noprogress", Arg.Clear bohne_refine_progress,
    "Do not use abstraction refinement");
   ("-nocaching", Arg.Clear usecaching,
    "Do not use caching");
   ("-noinstantiation", Arg.Clear bohne_useinstantiation,
    "Do not use quantifier instantiation heuristics");
   ("-nocontext", Arg.Clear bohne_usecontext,
    "Do not use context");
   ("-method", Arg.String add_class_method,
    "Analyze the given class.method\n" ^ 
      "    " ^ initialization_name ^ " checks initial condition\n" ^
      "    " ^ repcheck_name ^ " checks representation preservation");
   ("-class", Arg.String add_class,
    "Analyze the given class");
   ("-timeout", Arg.Int set_timeout,
    "<int> Set decision timeout (in seconds) for each decision procedure, default " ^ Printf.sprintf "%d" default_timeout);
   ("-nosastvc", Arg.Clear sastVC,
    "Do not use desugaring into simpler ast");
   ("-usedp", Arg.Rest add_usedp,
    "<IDs> specify the list of used decision procedures (cvcl|mona|spass)");
   ("-excludedp", Arg.Rest add_excludedp,
    "<IDs> specify the list of excluded decision procedures (cvcl|mona|spass)");
  ]

and print_usage() : unit =
  print_string usage_msg

and cmd_line_error (msg : string) =
  Arg.usage cmd_options usage_msg;
  Util.warn ("Command line option error: " ^ msg)

and get_class_ident (s : string) : (string * string) list = 
  match Util.split_by "." s with
    | [cn;mn] -> [(cn,mn)]
    | _ -> 
	Util.warn ("Error parsing class.ident specification.");
	Arg.usage cmd_options usage_msg;
	[]
and add_class_method (s : string) : unit =
  add_methods (get_class_ident s)
and set_timeout (t : int) : unit =
  (timeout := t)
and add_usedp id = 
  match Str.split (Str.regexp ":") id with
    | [] -> cmd_line_error "empty usedp option"
    | name::options -> 
	let opts = ListLabels.fold_left ~f:split_equal ~init:(StringMap.empty) options in
	  usedps := (name, opts)::!usedps

let _ =
  print_endline "Bohne standalone version.";
  Arg.parse cmd_options add_javaFile usage_msg;
  try
    (* disable VC generator and activate Bohne with refinement by default *)
    
    CmdLine.callbohne := true;
    CmdLine.bohne_refine := true;
    let res = invoke () in
    if res then exit 0 else exit 1
  with exc -> 
    print_string ("Exception thrown:\n" ^ Printexc.to_string exc ^ "\n");
    exit 1
