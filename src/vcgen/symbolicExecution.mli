(** Symbolic Execution

@author Lionel Rieg (lionel.rieg\@ens-lyon.fr) *)


type variables =
    (Form.ident * Form.form) list * (Form.ident * Form.form list) list
(** Two maps that bind variables to their values and arrays to their
    dimensions. *)

type state = {
  values : (Form.ident * Form.form) list;
  arrays : (Form.ident * Form.form list) list;
  path_condition : Form.form list;
  verification_condition : Form.form list;
  returned : bool;
}
(** The abstract state of a program: a map between variable names and their
    symbolic values, along with the current path conditions. We use a special
    record for arrays to ensure allocation and boundary conditions. *)


(** {6 Special values handling} *)


val undef_prefix : string
(** Prefix used for the value of undefined variables. *)

val unknown_prefix : string
(** Prefix used for unknown but defined values. *)

val init_prefix : string
(** Prefix used for the initial values. *)

val init : Form.ident -> Form.form
(** Initial value for a variable at the beginning of the program. *)

val any : Form.ident -> Form.form
(** Arbitrary assigned value of a variable after a 'havoc' command. Used to
    handle 'havoc' commands and global declarations. *)

val mk_undef : Form.ident -> Form.ident * Form.form
(** Undefined value for a variable which was allocated but not assigned to. *)

val mk_unknown : Form.ident -> Form.ident * Form.form
(** Uknown but defined value for a variable, for instance after a loop. *)

val is_defined : Form.form -> bool
(** Test wether the value is defined (ie has been assigned). *)


(** {6 Manipulating and printing states} *)


val add_path_condition : Form.form -> state -> state
(** Add a path condition to a state. *)

val run : (state -> state) -> state -> state
(** [run action state] tests if the computation is over in [state] and
    if not, executes [action state]. *)

val apply_subst : FormUtil.substMap -> state -> state
(** Apply a substitution on a state. Definition names are left unchanged. *)

val merge_state : state -> state -> state
(** Merge two states by adding or replacing new field values. The data of
    the first state have precedence in case of conflict.*)

val purify_states : (Form.ident -> bool) -> state list -> state list
(** Filter a state list by eliminating unmodified variables and variables
    that satisfy an elimination predicate. *)

val print_state : Form.ident -> state -> unit
(** Print a symbolic execution state. *)

val print_paths : Form.ident -> Form.ident -> state list -> unit
(** [print_paths impl proc_name state_list] prints all states in
    [state_list], assuming they are the symbolic executions of procedure
    [proc_name] in implementation module [impl]. *)

val show_vars : variables -> string
(** Show initial variables: values and arrays. *)

val show_state : string -> state -> string
(** [show_state pad state] fully shows the symbolic execution state [state],
    indented by [pad]. *)


(** {6 Symbolic execution of basic commands} *)


val exec_Skip : state -> state
(** Symbolically execute a 'skip' command. *) 

val exec_Hint : Ast.hint -> state -> state
(** Symbolically execute a 'hint' command. *) 

val exec_VarAssign : Ast.assign_command -> state -> state
(** Symbolically execute an assignement command. *) 

val exec_Alloc : Ast.alloc_command -> state -> state
(** Symbolically execute an allocation command. *) 

val exec_ArrayAlloc : Ast.array_alloc_command -> state -> state
(** Symbolically execute an array allocation command. *) 

val exec_Assert : Ast.hint_annot_form_command -> state -> state
(** Symbolically execute an 'assert' command. *) 

val exec_NoteThat : Ast.hint_annot_form_command -> state -> state
(** Symbolically execute a 'noteThat' command. *) 

val exec_Assume : Ast.annot_form_command -> state -> state
(** Symbolically execute an 'assume' command. *) 

val exec_Split : Ast.annot_form_command -> state -> state
(** Symbolically execute a 'split' command. *) 

val exec_Havoc : Ast.havoc_command -> state -> state
(** Symbolically execute a 'havoc' command. *) 

val exec_ProcCall : Ast.proc_call -> state -> state list
(** Symbolically execute a procedure call. *) 

val exec_bc : Ast.basic_command -> state -> state list
(** Symbolically execute the basic command on all the given states and
    return the resulting state list. *)


(** {6 Symbolic execution of full commands} *)


val exec_Seq : Ast.command list -> state list -> state list
(** Symbolically execute a sequence of commands. *)

val exec_Choice : Ast.command list -> state list -> state list
(** Symbolically execute a 'choice' command. *)

val exec_If : Ast.if_command -> state list -> state list
(** Symbolically execute an 'if' command. *)

val exec_Loop : Ast.loop_command -> state list -> state list
(** Symbolically execute a loop. *)

val exec_Return : Ast.return_command -> state list -> state list
(** Symbolically execute a 'return' command. *)

val exec_command : Ast.command -> state list -> state list
(** Symbolically execute the command from the given state and return the
    new state. We use a list of states to deal with all paths in parallel. *)

val local_decl : variables -> Ast.var_decl -> variables
(** Process a local variable declaration of a procedure. *)

val global_decl : variables -> Ast.global_def -> variables
(** Process the global declaration of a variable. *)

val make_mod_vars : Form.ident -> variables
(** Create the common module variables and store them. Used to initialize
    state for procedure analysis. *)

val exec_proc : Form.ident -> Form.ident -> state list
(** [exec_proc ] finds a procedure in a module by its name, then execute it. *)

val analyse_method : Form.ident -> Form.ident -> unit
(** Analyse a method and prints the symbolic result states. *)

val analyse_class : Form.ident -> unit
(** Analyse all methods of a class and prints their symbolic result states. *)

val do_it : Ast.program -> Common.analysis_task -> bool
(** Process a task. Ignore lemmas with a warning then analyse required
    methods and classes. If no method or class are given, analyse the whole 
    program. *)
