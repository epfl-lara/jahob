(** Options for Bohne *)

(** guarantee progress of abstraction refinement *)
let opt_refine_progress = ref true

(** do not split Boolean heaps *)
let opt_no_splitting = ref false

(** derive predicates automatically *)
let opt_derive_preds = ref true

(** use abstraction refinement *)
let opt_refine = ref true

(** use more precise abstraction *)
let opt_extra_precise = ref false

(** use quantifier instantiation for context formulas *)
let opt_use_instantiation = ref true
let opt_use_context = ref true

(** compute invariant for return points *)
let opt_abstract_final = ref false

(** output file for final ART constructed by Bohne *)
let opt_art_file = ref "art.dot"
let opt_print_art = ref false

let opt_derive_iterators = ref true

let opt_propagate_preconditions = ref true

let opt_fast_abstraction = ref true

let opt_context_per_state = ref false

let opt_complete_prover = ref true

let opt_check_soundness = ref false

let opt_lazy_abstraction = ref false

let readCmdLine () =
  opt_refine := !CmdLine.bohne_refine;
  opt_refine_progress := !CmdLine.bohne_refine_progress;
  opt_no_splitting := !CmdLine.bohne_no_splitting;
  opt_derive_preds := !CmdLine.bohne_derive_preds;
  opt_extra_precise := !CmdLine.bohne_extra_precise;
  opt_use_instantiation := !CmdLine.bohne_useinstantiation;
  opt_use_context := !CmdLine.bohne_usecontext;
  opt_abstract_final := !CmdLine.bohne_abstract_final;
  opt_art_file := !CmdLine.bohne_art_file;
  opt_print_art := !CmdLine.bohne_print_art
  
