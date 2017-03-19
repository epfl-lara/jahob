(** Commutativity Analysis *)

(** Perform the commutativity analysis to determine wether calls inside a
    methods can be parallelised.

    Modifies the behaviour of the following flags:
      -commute  the commutativity condition,
                currently only equality of fileds or variables
      -ignoreassert  if used with the string Commute,
                     disable verification of assertions for validity of code


@authors Lionel Rieg (lrieg\@csail.mit.edu) and Karen Zee (kkz\@mit.edu)
 *)


(** {6 Types and constant values definitions} *)


type proc_def_env = Ast.impl_module * Ast.proc_def * Form.ident 
(** Type for 'usable' method definition: the module it is from,
    the definition itself and and the qualified name. *)

val ignore_asserts : string
(** The parameter to give to '-ignoreassert' to avoid the assertion checking *)


(** {6 Printing and variable name handling} *)


val print_ident_list : int -> string -> Form.ident list -> unit
(** Print the identifier list if the debug level is high enough. *)

val print_extent : int -> string -> proc_def_env list -> unit
(** Print the names of a procedure list. The optional parameter allows to
    precise from which level of debugging the message starts gfetting
    printed. *)

val show_rename_map : FormUtil.substMap -> string
(** Create a printable string from a rename map. *)

val orderA_suffix : string
(** Suffix denoting first computation order. *)

val orderB_suffix : string
(** Same as [orderA_suffix] for the second computation order. *)

val orderA_id : Form.ident -> Form.ident
(** Transform an identifier to particularise it for the first computation
    order by appending [orderA_suffix]. *)

val orderB_id : Form.ident -> Form.ident
(** Same as [orderA_id] for the second computation order. *)

val commutativity_prefix : string
(** Prefix used as basis for generating variables during commutativity
    analysis. *)

val init_suffix : string
(** Suffix for distinguishing initial (old) values. *)

val commute_id : unit -> Form.ident
(** Generate a fresh variable for commutativity analysis. *)

val is_commute_id : Form.ident -> bool
(** Determine wether the given identifier is an automatically generated
    variable for commutativity analysis. (with or without a suffixes denoting
    initial values and/or which execution) *)

val is_this : Ast.var_decl -> bool
(** Test wether the given variable declaration is the receiver of current
    computation. *)

val mk_id : Ast.var_decl -> Form.ident
(** Make a new variable out of the given identifier. *)

val init : Form.ident -> Form.ident
(** Transform the identifier into an initial value. *)

val is_init_id : string -> bool
(** Test wether the identifier is an initial value. *)


(** {6 Renaming operations} *)


val rename_vars : Form.ident list -> (Form.ident * Form.form) list
(** Create a renaming map that associate each name with a fresh variable. *)

val mk_rename_map : Form.ident list ->
       (Form.ident -> Form.ident) -> FormUtil.substMap
(** Same as [mk_rename_map] but on a identifier list, not on a procedure
    definition. *)

val mk_rename_map_for_pd : Ast.proc_def ->
       (Form.ident -> Form.ident) -> FormUtil.substMap
(** Returns a rename map for the local variables of a procedure created by
    applying the given transformation, together with the list of new
    identifiers. *)

val replace_if_match : FormUtil.substMap -> Form.ident -> Form.ident
(** Apply the name substitution on the variable identifier. *)

val typeForm_of_typedIdent : Form.typedIdent -> Form.typeForm
(** Return the type of a typed identifier. *)

val rename_ident_of_typedIdent : FormUtil.substMap ->
       Form.typedIdent -> Form.typedIdent
(** Same as replace_if_match for a typed identifier. *)

val rename_assign_command : FormUtil.substMap ->
       Ast.assign_command -> Ast.assign_command
(** Apply a renamig substitution on an assign command. *)

val rename_alloc_command : FormUtil.substMap ->
       Ast.alloc_command -> Ast.alloc_command
(** Apply a renaming substitution on an allocation command. *)

val rename_array_alloc_command : FormUtil.substMap ->
       Ast.array_alloc_command -> Ast.array_alloc_command
(** Apply a renaming substitution on an array allocation command. *)

val rename_hint_annot_form_command : FormUtil.substMap ->
       Ast.hint_annot_form_command -> Ast.hint_annot_form_command
(** Apply a renaming substitution on an [assert] or [noteThat] command. *)

val rename_annot_form_command : FormUtil.substMap ->
       Ast.annot_form_command -> Ast.annot_form_command
(** Apply a renaming substitution on an [assume] or [split] command. *)

val rename_havoc_command : FormUtil.substMap ->
       Ast.havoc_command -> Ast.havoc_command
(** Apply a renaming substitution on a [havoc] command. *)

val rename_proc_call : FormUtil.substMap -> Ast.proc_call -> Ast.proc_call
(** Apply a renaming substitution on a procedure call. *)

val rename_hint : FormUtil.substMap -> Ast.hint -> Ast.hint
(** Apply a renaming substitution on a [hint] command. *)

val combine_rename_maps : FormUtil.substMap ->
       FormUtil.substMap -> FormUtil.substMap
(** Merge two maps. The second one has precedence in case of conflict. *)

val rename_bc : FormUtil.substMap -> Ast.basic_command -> Ast.basic_command
(** Apply a renaming substitution on a basic command. *)


(** {6 Testing properties of the program and extraction of infomation} *)


val no_calls : Form.form -> bool
(** Formulas do not contain method invocations. *)

val ucommand : Ast.basic_command -> bool
(** Return true if the basic command is a update command (ie, not a
    non inlined procedure call). *)

val iform : Form.ident list -> Form.form -> bool
(** Test wether the formula is valid for invocation method. *)

val icommand : Form.ident list -> Form.ident list -> Ast.basic_command -> bool
(** Test wether a basic command is an invocation command. An invocation
    command may invoke operations but may not access the receiver. *)

val test_command :
      ?testseq:((Ast.command -> bool) ->
                  (Form.form -> bool) -> bool -> Ast.command list -> bool) ->
      ?testch:((Ast.command -> bool) ->
                 (Form.form -> bool) -> bool -> Ast.command list -> bool) ->
      ?testif:((Ast.command -> bool) ->
                 (Form.form -> bool) -> bool -> Ast.if_command -> bool) ->
      ?testloop:((Ast.command -> bool) ->
                   (Form.form -> bool) -> bool -> Ast.loop_command -> bool) ->
      (Ast.basic_command -> bool) ->
      (Form.form -> bool) -> bool -> Ast.command -> bool
(** Use tests on basic commands and formulae to generate the same test on
    command in the obvious way. Yet, all meaningful commands can have a
    different treatment with the appropriate optionnal argument. The boolean 
    arguemtn is a default value used for handling [assuming], [pickAny] and
    empty [return] statements. *)

val imethod : proc_def_env -> bool
(** Test and print if the method is an invocation method. An invocation
    method invokes operations and does not perform accesses to the
    receiver. *)

val umethod : proc_def_env -> bool
(** Same as imethod for update methods. An update method performs
    accesses to the receiver and does not invoke operations. *)

val check_decomp : proc_def_env -> bool
(** Check if the given method is either invocation or update. *)


val is_trivial : Form.form -> bool
(** Recognize completely trivial formulae. *)

val filter_trivial : Form.form -> bool
(** Eliminate trivial formulae. *)

val no_calls_inlined : Ast.basic_command -> bool
(** Test wether there is no call to an inlined procedure of the given list
    in the basic command. *)

val no_calls_inline : Ast.proc_def -> bool
(** Same as no_calls_inlined for a procedure definition. *)

val get_proc_info : Form.ident * Form.ident -> proc_def_env
(** Get information on the procedure: its module, definition and full name. *)

val get_proc_def : Form.ident * Form.ident -> Ast.proc_def
(** Same as get_proc_info but return only the procedure definition. *)


(** {6 Creating auxiliary formulae} *)


val mk_null_check : Form.ident -> Ast.command
(** Create a assert command which checks that the given variable is not null. *)

val mk_assumes_from_vd : Ast.var_decl -> Form.ident -> Ast.command list
(** Create an assume command which assumes the existence and type of a copy
    of the given Java variable and its Java type. *)

val mk_proccall : Ast.impl_module ->
      Ast.proc_def -> Ast.command * Form.ident list
(** Create a procedure call out of the procedure definition and return the
    command with all appropriate assumes for arguments plus result and argument
    names. *)

val mk_fld_eqs : Form.ident -> Form.form
(** Create a formula saying that the given field have the same value for
    all current objects. *)

val mk_init_fld_eqs : Form.ident -> Form.form
(** Same as [mk_fld_eqs] but for initial objects. *)

val mk_lv_eqs : Form.ident -> Form.form
(** Create a formula saying that the parameter variable is the same in both
    execution orders. *)

val mk_init_var_eqs : Form.ident -> Form.form
(** Same as [mk_lv_eqs] but for initial variables. *)


(** {6 Commutativity analysis} *)


val prove : string -> Form.form list -> int
(** Try to prove the given list of formulae with debug printing. Return the
    number of failed verifications. *)

val get_callees : ?name:Form.ident ->
      Ast.proc_def -> (Form.ident * Form.ident) list
(** Return the list of methods (module name, method name) that the given
    procedure calls in any of its execution. The optionnal parameters is
    the name of the procedure, to be able to qualifiy it. *)

val compute_callee_multiset : proc_def_env -> Ast.proc_call list
(** Return the list of direct calls with repetition of the procedure with
    their arguments and receivers. *)

val compute_extent : proc_def_env -> proc_def_env list
(** Compute all methods recursively called during a call to the given
    method. (transitive cloture of [get_callees]) *)

val extract_invocation_section : Ast.proc_def ->
       FormUtil.substMap -> Ast.command
(** Extract the invocation part of the method, ie no state update. *)

val extract_code : Ast.impl_module ->
       Ast.proc_def ->
       (Form.ident -> Form.ident) -> Ast.command * Form.ident list
(** Extract the relevant code: either the whole body for update methods or
    the invocation part for the others. *)

val equivalent_final : Form.ident list -> Form.form -> Form.form -> bool
(** Check if the variables and fields present at the end are the same in
    both execution orders. *)

val object_sections_commute : Ast.impl_module ->
      Ast.impl_module -> Ast.proc_def -> Ast.proc_def -> bool
(** Test wether the given methods commute, assuming they both have a non
    empty object section or calls to inlined methods. *)

val check_multiset : proc_def_env -> proc_def_env -> bool
(** Check if the procedure calls are the same (ie same method, arguments
    and receiver) in both execution orders. *)

val methods_commute : proc_def_env -> proc_def_env -> bool
(** Test wether the given methods commute and print the result. *)

val extent_commute : proc_def_env list ->
      bool * Form.ident list * proc_def_env list
(** Apply commutativity analysis on the given list of methods, assuming they
    have the right shape. *)

val check_commute : (Form.ident * Form.ident) list -> bool
(** Test the shape of the methods before doing commutativity analysis. *)

val run_class : Form.ident -> bool
(** Perform commutativity analysis on all methods of a class. *)

val run_commute : Ast.program -> Common.analysis_task -> bool
(** Perform commutativity analysis on a task. *)
