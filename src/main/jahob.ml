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

let pretty_print_unit (how : string) (unit : Syntax.compilation_unit) : unit = 
  let opts = Common.options_of_string how in
  let old_public_only = !Pretty.public_only in
  let _ = (Pretty.public_only := (Common.flag_positive ~o:opts "public" )) in
  let _ = Pretty.print Format.std_formatter unit in (* actual printing *)
  Pretty.public_only := old_public_only

let pretty_print_java () : unit = 
  List.iter
    (fun how -> (List.iter (pretty_print_unit how) !units))
    !CmdLine.printJavaOpts

let invoke () : bool =
  parse_java_files (std_java_files @ !CmdLine.javaFiles);
  Debug.msg 
    (Printf.sprintf "Number of compilation units processed: %d.\n"
       (List.length !units));
  Util.fail_if_warned("PARSING FAILED.");
  let _ = pretty_print_java() in
  let _ = (Javajast.number_of_assumes := 0) in
  let (p,task) = Javajast.joust2jast !units (CmdLine.get_task()) in
  let u = Jastjava.jast2joust p in
  Util.fail_if_warned("CONVERSION TO Jast FAILED.");
  let _ = if !CmdLine.printJast then
    (Util.msg "Resulting declarations:\n";
     Pretty.print Format.std_formatter u) else() in
  let ast = Jast2ast.c_program p in
  Util.fail_if_warned("CONVERSION TO Ast FAILED.");
  let _ = if !CmdLine.printAst then 
    print_string (PrintAst.pr_program ast) else() in
  let _ = if !CmdLine.armcOut then 
    ArmcI.translate_program ast else() in
  let _ = if !CmdLine.static then 
    Static.analyze_program ast task.Common.task_classes in
  let _ = Encapsulation.encapsulation_analysis ast in
  let _ = if !CmdLine.sastVC then 
    (let sast = Sast.ast2sast ast in
       if !CmdLine.printSAst then
	 print_string (PrintAst.simplified_program sast))
  in
    (if !CmdLine.verify then ()
     else 
       Util.amsg "*** VERIFICATION WILL FAIL, -noverify option given.\n");
    let ok = (if !CmdLine.commute
	      then Commute.run_commute ast task
	      else Analyze.analyze ast task) in
    let assume_report = 
      if !Javajast.number_of_assumes = 0 then ""
      else if !Javajast.number_of_assumes = 1 then 
	" (modulo one assume statement)"
      else Printf.sprintf " (modulo %d assume statements)" 
	!Javajast.number_of_assumes
    in
    let _ = if ok then Util.amsg 
      ("\n0=== Verification SUCCEEDED" ^ assume_report ^ ".\n")
    else Util.amsg "\n-1=== Verification FAILED.\n" in
      ok

let print_info() =
  (Util.msg 
"     _       _           _                  _____
    | | __ _| |__   ___ | |__              /     \\
 _  | |/ _` | '_ \\ / _ \\| '_ \\       x <==|  (J)  |===.
| |_| | (_| | | | | (_) | |_) |     ======+=======+===\"  F
 \\____/\\__,_|_| |_|\\___/|_.__/             \\_____/  

";
   Debug.msg "
                            / \\  //\\
             |\\___/|      /   \\//  \\\\
            /0  0  \\__  /    //  | \\ \\
           /     /  \\/_/    //   |  \\  \\                 
           @_^_@'/   \\/_   //    |   \\   \\
           //_^_/     \\/_ //     |    \\    \\
        ( //) |        \\///      |     \\     \\
      ( / /) _|_ /   )  //       |      \\     _\\
    ( // /) '/,_ _ _/  ( ; -.    |    _ _\\.-~        .-~~~^-.
  (( / / )) ,-{        _      `-.|.-~-.           .~         `.
 (( // / ))  '/\\      /                 ~-. _ .-~      .-~^-.  \\
 (( /// ))      `.   {            }                   /      \\  \\
  (( / ))     .----~-.\\        \\-'                 .~         \\  `. \\^-.
 [BUGS]            ///.----..>        \\          _ -~             `.  ^-`  ^-_
                  ///-._ _ _ _ _ _ _}^ - - - - ~                  ~-- ,.-~/.-~
Formal methods are the future of computer science---always have been, always will be.

";
   flush_all())

let _ =
  Util.msg("[Jahob Version -0.44]\n");
  CmdLine.process ();
  print_info();
  try 
    let res = invoke() in
      if res then exit 0 else exit 1
  with exc -> 
    print_string ("Jahob exception thrown:\n" ^ Printexc.to_string exc ^ "\n");
    exit 1
