(** Command line processing and invocation options. *)

open Common


(** {6 Parameters with default values} *)


let printAst = ref false
let armcOut = ref false
let printSAst = ref false
let printJast = ref false
let printVCs = ref false
let printCounts = ref false
let pvcPrefix = ref ""
let typecheck = ref true

let verify = ref true
let sastVC = ref true
let tokens = ref false
let failfast = ref false
let noisabelle = ref false
let nocoq = ref false
let notptp = ref false
let callbohne = ref false
let inferLoopInvs = ref false
let inferMinimize = ref false
let driver_method = ref ""
let interpret = ref false
let usedps = ref []
let excludedps = ref []
let checkHidden = ref false

let background = ref true
let minasm = ref false
let default_timeout = 10
let timeout = ref default_timeout
let inferTimeOut = ref 1200

let useslicing = ref true
let usecaching = ref true
let storecache = ref false
let cache_file_name = ref ""

let concurrent_provers = ref true
let maxvcpar = ref 0

let proofstmts = ref true
let novcsplit = ref false

(* Split the antecedent disjunctively in case the original sequent can't be proven. *)
let tryHard = ref false

let static = ref false

(** Info for Java pretty printing *)

let (printJavaOpts : ((string list) ref)) = ref []
let add_java_print_opt (opt : string) : unit =
  (printJavaOpts := opt :: !printJavaOpts)


(** {4 Flags for Bohne} *)


(** guarantee progress of abstraction refinement *)
let bohne_refine_progress = ref true

(** do not split Boolean heaps *)
let bohne_no_splitting = ref false

(** derive predicates automatically *)
let bohne_derive_preds = ref true

(** use abstraction refinement *)
let bohne_refine = ref true

(** use more precise abstraction *)
let bohne_extra_precise = ref false

(** use quantifier instantiation for context formulas *)
let bohne_useinstantiation = ref true
let bohne_usecontext = ref true

(** compute invariant for return points *)
let bohne_abstract_final = ref false

(** output file for final ART constructed by Bohne *)
let bohne_art_file = ref "art.dot"
let bohne_print_art = ref false

(** Name of the output file of armc interface  *)

let armcfile = ref "armcout.armc"

let jahob_unsound = ref false
let bounded_loop_unroll = ref false
let unroll_factor = ref 1
let ignore_asserts : string list ref = ref []
let prove_only_asserts : string list ref = ref []
let simple_call_site_frames = ref false
let builtinstd = ref false

let commute = ref false
(* Force inlined and non parallel method for commutativity analysis *)
let inlined : string list ref = ref []
let notParallel : (string * string) list ref = ref []
let noInlining = ref false

  (** {6 Command line processing} *)


let (lemmas_to_prove : (string * string) list ref) = ref []
let add_lemmas (new_lemmas : (string * string) list) : unit =
  (lemmas_to_prove :=
     new_lemmas @ !lemmas_to_prove)

let (methods_to_analyze : (string * string) list ref) = ref []
let add_methods (new_methods : (string * string) list) : unit =
  (methods_to_analyze :=
     new_methods @ !methods_to_analyze)

let add_prove_only_assert (s : string) : unit =
  (prove_only_asserts := s :: !prove_only_asserts)

let add_ignore_assert (s : string) : unit =
  (ignore_asserts := s :: !ignore_asserts)

let (classes_to_analyze : string list ref) = ref []
let add_class (s : string) : unit =
  (classes_to_analyze := s :: !classes_to_analyze)

let get_task () = {
  task_lemmas = List.rev !lemmas_to_prove;
  task_methods = List.rev !methods_to_analyze;
  task_classes = List.rev !classes_to_analyze;
}

(** List of JAVA files to be processed *)
let (javaFiles : string list ref) = ref []

(** Add a file to the list of JAVA file to be processed *)
let add_javaFile (file : string) : unit = 
  javaFiles := file :: !javaFiles

(** Suffix added to a class for initialisation condition *)
let initialization_name = "_INIT"

(** Suffix added to a class for representation condition *)
let repcheck_name = "_REP"

let set_infer_with_options (s : string) : unit =
  inferLoopInvs := true;
  let options = Str.split (Str.regexp ":") s in
  let opts = ListLabels.fold_left ~f:split_equal 
    ~init:(StringMap.empty) options in
    (* minimize loop invariant? *)
    inferMinimize := flag_positive ~o:opts "Minimize";
    (* use interpretation to perform filtering? *)
    interpret := flag_positive ~o:opts "Interpret";
    if !interpret then
      driver_method := StringMap.find "Interpret" opts;
    (try
       inferTimeOut := int_of_string (StringMap.find "TimeOut" opts)
     with Not_found -> ())
    
let add_excludedp id = excludedps := id::!excludedps

let equivConds : (string list) ref = ref []

let setupCommute (s : string) : unit =
  commute := true;
  sastVC := false; (* avoid aving to use the '-nosastvc' option *)
  Common.parseall := true;
  equivConds := !equivConds @ [s]

let setupInlined (s : string) : unit =
  inlined := s :: !inlined

let setupNotParallel (s : string) : unit =
  notParallel := (Util.unqualify2 s) :: !notParallel
       

let setupPrintVCs (s : string) : unit =
  printVCs := true;
  pvcPrefix := s

let set_timeout (t : int) : unit = (timeout := t)
let set_maxvcpar (t : int) : unit = (maxvcpar := t)

(** Options for the command line *)
let rec cmd_options = 
  [("-v", Arg.Set Util.verbose,
    "Display verbose messages");
   ("-verbose", Arg.Set Util.verbose,
    "Display verbose messages");
   ("-debug", Arg.Set Debug.debugOn,
    "Display debugging messages");
   ("-debuglevel", Arg.Int Debug.set_debug_level,
    "<int> Adjust amount of debug messages, default "
    ^ Printf.sprintf "%d" !Debug.debug_level);
   ("-debugmodules", Arg.String Debug.set_debug_modules,
    "<modules> Turn on debug messages for a specific module (e.g. SmtPrint)");
   ("-java", Arg.String add_java_print_opt,
    "Pretty print Java source in specified way \
     (public = only public interface; xsym = use xsymbol tokens in formulas)");
   ("-jast", Arg.Set printJast,
    "Display intermediate Jast representation");
   ("-ast", Arg.Set printAst,
    "Display intermediate Ast representation");
   ("-sast", Arg.Set printSAst,
    "Display simplified Ast representation (requires -method)");
   ("-nosastvc", Arg.Clear sastVC,
    "Do not use desugaring into simpler ast when generating \
     verification conditions (some things will not work)");
   ("-sastvc", Arg.Set sastVC,
    "Use desugaring into simpler ast when generating verification conditions \
     (this is the default)");
   ("-printvc", Arg.String setupPrintVCs,
    "<prefix> Print verification conditions for each method to file \
     <prefix>_<class>_<file>.vc");
   ("-armcout", Arg.Set armcOut,
    "Translates the java program into ARMC input");
   ("-commute", Arg.String setupCommute,
    "Invokes commutivity analysis using equality of the given field(s) \
     or variable(s) as the equivalence condition");
   ("-inline", Arg.String setupInlined,
    "<method> Force Jahob to inline some methods when running \
     commutivity analysis");
   ("-notparallel", Arg.String setupNotParallel,
    "<method> Prevent Jahob from trying to parallelize these methods \
      when running commutivity analysis");
   ("-noinlining", Arg.Set noInlining,
    "Deactivate the inlining process when running commutivity analysis");
   ("-hidden", Arg.Set checkHidden,
    "Enforce the policy with regard to hidden objects");
   ("-notypecheck", Arg.Clear typecheck,
    "Do not typecheck formulas");
   ("-failfast", Arg.Set failfast,
    "Fail as soon as one proof obligation fails");
   ("-resilient", Arg.Set Util.resilient,
    "Continue even if a warning is emitted");
   ("-minasm", Arg.Set minasm,
    "Try to find minimal set of assumptions needed to prove valid obligations");
   ("-noverify", Arg.Clear verify,
    "No verification, just transform to intermediate form");
   ("-novcsplit", Arg.Set novcsplit,
    "Disable splitting of verification conditions and the internal prover");
   ("-noisabelle", Arg.Set noisabelle,
    "Turn off Isabelle invocation");
   ("-nocoq", Arg.Set nocoq,
    "Turn off Coq invocation");
   ("-novampire", Arg.Set notptp,
    "Turn off Vampire invocation"); 
   ("-nobackground", Arg.Clear background,
    "Do not generate verification condition background formula");
   ("-noconcurrency", Arg.Clear concurrent_provers,
    "Do not invoke external provers concurrently");
   ("-maxvcpar", Arg.Int set_maxvcpar,
    "Max number of forks for external provers for independent VC conjuncts");
   ("-nopreddiscovery", Arg.Clear bohne_derive_preds,
    "Do not discover predicates automatically in Bohne");
   ("-refine", Arg.Set bohne_refine,
    "Enable abstraction refinement in Bohne (default)");
   ("-norefine", Arg.Clear bohne_refine,
    "Disable abstraction refinement in Bohne");
   ("-abstractfinal", Arg.Set bohne_abstract_final,
    "Include final transitions in Bohne's fixed point computation");
   ("-noprogress", Arg.Clear bohne_refine_progress,
    "Do not use quantifier instantiation heuristics");
   ("-nosplitting", Arg.Set bohne_no_splitting,
    "Do not split Boolean heaps in Bohne");
   ("-nocaching", Arg.Clear usecaching,
    "Do not use caching");
   ("-noinstantiation", Arg.Clear bohne_useinstantiation,
    "Do not use quantifier instantiation heuristics");
   ("-nocontext", Arg.Clear bohne_usecontext,
    "Do not use context");
   ("-extraprecise", Arg.Set bohne_extra_precise,
    "Use more precise abstraction in Bohne");
   ("-printart", Arg.Set bohne_print_art,
    "Print Graphviz representation of abstract reachability tree \
     to given file");
   ("-cachefile", Arg.String ((:=) cache_file_name),
    "Use given file as soource for persistent cache");
   ("-storecache", Arg.Set storecache,
    "Store new cache entries to persistent cache");
   ("-method", Arg.String add_class_method,
    "Analyze the given class.method\n" ^ 
      "    " ^ initialization_name ^ " checks initial condition\n" ^
      "    " ^ repcheck_name ^ " checks representation preservation");
   ("-class", Arg.String add_class,
    "Analyze the given class");
   ("-lemma", Arg.String add_lemma,
    "Prove given named lemma");
   ("-bohne", Arg.Set callbohne,
    "Infer loop invariants using Bohne");
   ("-infer", Arg.String set_infer_with_options,
    "Infer loop invariants. (None|[TimeOut=<k>:Interpret=<driver>:Minimize])");
   ("-interpret", Arg.Set interpret,
    "Run interpreter. " ^
      "All invoked methods must also be specified using -method.");
   ("-builtinstd", Arg.Set builtinstd,
    "Use built-in classes instead of parsing them from library directory.");
   ("-unroll", Arg.Set bounded_loop_unroll,
    "Use bounded loop unrolling");
   ("-unrollfactor", Arg.Set_int unroll_factor,
    "Number of times to unroll loops");
   ("-simpcall", Arg.Set simple_call_site_frames,
    "Simplified call site frame conditions");
   ("-ignoreassert", Arg.String add_ignore_assert,
    "Ignore all assertions whose comment contains the given string");
   ("-assert", Arg.String add_prove_only_assert,
    "Ignore all assertions except those containing the given string");
   ("-printcounts", Arg.Set printCounts,
    "Print counts of Java, specification, and proof constructs");
   ("-ignoreproofstatements", Arg.Clear proofstmts,
    "Ignore all proof statements");
   ("-static", Arg.Set static,
    "Run instantiation analysis.");
   ("-timeout", Arg.Int set_timeout,
    "<int> Set decision timeout (in seconds) for each decision procedure, \
           default " ^ Printf.sprintf "%d" default_timeout);
   ("-usedp", Arg.Rest add_usedp,
    "<IDs> specify the list of used decision procedures \
     (cvcl|mona|isa{:(TimeOut=k|CompactSave|VerboseSave)}|coq|vampire|e|z3|\
     spass|bapa{:qfbapa|fullbapa})");
   ("-excludedp", Arg.Rest add_excludedp,
    "<IDs> specify the list of excluded decision procedures (cvcl|mona|isa)");
   ("-tryHard", Arg.Set tryHard,
    "Invest really more time in attempts to prove sequent. Currently, split the antecedent using the distributive law in case the original antecedent is too large to analyze.");
   ("-noTryHard", Arg.Clear tryHard,
    "Don't invest additional time in attempts to prove sequent. Currently, just fail in case the original antecedent is too large to analyze.");
  ]

and usage_msg =
  ("Usage:\n  " ^ Sys.argv.(0) ^ 
     " [-v] [-jast] [-ast] [-isatype] [-noverify] [-nobackground] \
       [-tryHard|-noTryHard] [-method class.method] [-class class] <inputJavaFiles> \
       [(-usedp | -excludedp) <IDs>]\n")

(** Print the usage message *)
and print_usage () : unit = print_string usage_msg

(** Print usage and warn of the error message given *)
and cmd_line_error (msg : string) =
  Arg.usage cmd_options usage_msg;
  Util.warn ("Command line option error: " ^ msg)

(** Transform a "class.ident" name into a list containing the couple
    "(class, ident)" *)
and get_class_ident (s : string) : (string * string) list = 
  match Util.split_by "." s with
    | [cn;mn] -> [(cn,mn)]
    | _ -> 
	Util.warn ("Error parsing class.ident specification.");
	Arg.usage cmd_options usage_msg;
	[]

and add_class_method (s : string) : unit = add_methods (get_class_ident s)

and add_lemma (s : string) : unit = add_lemmas (get_class_ident s)

and check_add_ignore_assert (s : string) : unit =
  if s="" then 
    (Util.warn ("Cannot specify empty ignore assert!");
     Arg.usage cmd_options usage_msg)
  else add_ignore_assert s
and add_usedp id = 
  match Str.split (Str.regexp ":") id with
    | [] -> cmd_line_error "empty usedp option"
    | name::options -> 
	let opts = options_of_string (String.concat ":" options) in
	  usedps := (name, opts)::!usedps

(** Check if the set of current options preserves soundness *)
let check_soundness () : unit =
  let unsoundness_list =
    [(!bounded_loop_unroll, "bounded loop unrolling");
     (!simple_call_site_frames, "simplified call site frame conditions");
     (!ignore_asserts <> [] || !prove_only_asserts <> [], "assertion ignoring")]
  in
  let _ = (jahob_unsound := false) in
  let rec check lst =
    match lst with
      | [] -> ()
      | (unsound_opt_on,description)::lst1 ->
	  ((if unsound_opt_on then 
	    (Util.msg("(!) Unsound option turned on: '" ^ description ^ "'\n");
	     jahob_unsound := true)
	    else ());
	   check lst1) in
  let _ = check unsoundness_list in
    if !jahob_unsound then 
      Util.amsg("Jahob results are unsound \
                 due to selected verification parameters.\n")
    else ()

(** Process command line and set global variables. *)
let process () : unit =
  Arg.parse cmd_options add_javaFile usage_msg;
  check_soundness ()
