(** Strongest postcondition path with or without existential binding of
    intermediate values and assertions

@author Lionel Rieg (lrieg\@csail.mit.edu) and Karen Zee (kkz\@mit.edu) *)

val sp_Skip : Form.form -> Form.form
(** [sp_Skip f] computes the postcondition for the [Skip] operation under
    precondition [f]: [\{ f \} Skip \{ f \}] (nothing to do). *)

val sp_Hint : Ast.hint -> Form.form -> Form.form
(** [sp_Hint f] computes the postcondition for the [Hint] operation under
    precondition [f]: [\{ f \} Hint h \{ f \}] (nothing to do since a hint
    is a special ast for Bohne). *)

val sp_VarAssign : Ast.assign_command -> Form.form -> Form.form
(** [sp_VarAssign ac f] computes the postcondition for the [VarAssign ac]
    operation under precondition [f]: [\{ f \} x := e \{ x = e\[x0/x\] ;
    f\[x0/x\] \}]. *)

val sp_Alloc : Ast.alloc_command -> Form.form -> Form.form
(** [sp_Alloc ac f] computes the postcondition for the [Alloc ac] operation
    under precondition [f]: [\{ f \} x := new T() \{ x \in Alloc ; x : T ;
    x <> null ; f \}]. *)

val sp_ArrayAlloc : Ast.array_alloc_command -> Form.form -> Form.form
(** [sp_ArrayAlloc aac f] computes the postcondition for the [ArrayAlloc
    aac] operation under precondition [f]: [\{ f \} x := new T\[n_1, ... ,
    n_k\] \{ x \in Alloc ; x : T ; x <> null ; "x.length = n_1" ; f \}].
    Currently, only uni-dimensional arrays are supported. *)

val sp_Assert : Ast.hint_annot_form_command -> Form.form -> Form.form
(** [sp_Assert c f] computes the postcondition for the [Assert c] operation
    under precondition [f]: [\{ f \} assert h \{ f \}] (we don't check
    asserts, but that's ok for inference). *)

val sp_NoteThat : Ast.hint_annot_form_command -> Form.form -> Form.form
(** [sp_NoteThat c f] computes the postcondition for the [NoteThat c]
    operation under precondition [f]: [\{ f \} noteThat x \{ f \}]
    ([noteThat x] desugars into [assert x; assume x]. Again, assert not
    checked). *)

val sp_Assume : Ast.annot_form_command -> Form.form -> Form.form
(** [sp_Assume ac f] computes the postcondition for the [Assume] operation
    under precondition [f]: [\{ f \} assume h \{ f \}] (we don't check
    assume statement, but that's ok for inference). *)

val sp_Split : Ast.annot_form_command -> 'a -> Form.form
(** [sp_Split s f] computes the postcondition for the [Split s] operation
    under precondition [f]: [\{ f \} split h \{ f \}]. Again, assert not
    checked. ([Split x] desugars into [Assert x; Havoc *; Assume x]). *)

val sp_Havoc : Ast.havoc_command -> Form.form -> Form.form
(** [sp_Havoc hc f] computes the postcondition for the [Havoc hc] operation
    under precondition [f]: [\{ f \} havoc x_1, \dots, x_k suchThat c_1,
    ... , c_n \{ c_i ; EX x_i. c_j ; f \}]. *)

val sp_ProcCall : Ast.proc_call -> Form.form -> Form.form
(** At that point, procedure calls should be desugared, so [sp_ProcCall pc
    f] returns [Failure "LoopInvariantInference: ProcCall should be
    desugared.\n"]. *)

val sp_bc : Ast.basic_command -> Form.form -> Form.form
(** [sp_bc bc f] computes the postcondition for the basic command [bc]
    under precondition [f]. Since we are only using this for inference, we
    don't have to check asserts when we get to them.  *)

exception Invariant_violation

val sp_unrolled : Form.form -> Ast.command -> int -> bool
(** [sp_unrolled f c i] returns [true] iff no invariant violation occurs in
    program [c] with loop-unrolling of order [i] for invariant-free loops. *)


(** {6 Full post-condition computation for each kind of basic commands}  *)


val sp_Skip_asserts :
  Form.form * Form.form list -> Form.form * Form.form list
(** [sp_Skip f] computes the postcondition for the [Skip] operation under
    precondition [f]: [\{ f \} Skip \{ f \}]. *)

val sp_Hint_asserts :
  Ast.hint -> Form.form * Form.form list -> Form.form * Form.form list
(** [sp_Hint f] computes the postcondition for the [Hint] operation under
    precondition [f]: [\{ f \} Hint h \{ f \}]. *)

val sp_VarAssign_asserts :
  Ast.assign_command ->
  Form.form * Form.form list -> Form.form * Form.form list
(** [sp_VarAssign ac f] computes the postcondition for the [VarAssign ac]
    operation under precondition [f]: [\{ f \} x := e \{ x = e\[x0/x\] ;
    f\[x0/x\] \}]. *)

val sp_Alloc_asserts :
  Ast.alloc_command ->
  Form.form * Form.form list -> Form.form * Form.form list
(** [sp_Alloc ac f] computes the postcondition for the [Alloc ac] operation
    under precondition [f]: [\{ f \} x := new T() \{ x \in Alloc ; x : T ;
    x <> null ; f \}]. *)

val sp_ArrayAlloc_asserts :
  Ast.array_alloc_command ->
  Form.form * Form.form list -> Form.form * Form.form list
(** [sp_ArrayAlloc aac f] computes the postcondition for the [ArrayAlloc
    aac] operation under precondition [f]: [\{ f \} x := new T\[n_1, \dots,
    n_k\] \{ x \in Alloc ; x : T ; x <> null ; "x.length = n_1" ; f \}]. *)

val sp_Assert_asserts :
  Ast.hint_annot_form_command ->
  Form.form * Form.form list -> Form.form * Form.form list
(** [sp_Assert c f] computes the postcondition for the [Assert c] operation
    under precondition [f]: [\{ f \} assert h \{ f \}]. *)

val sp_NoteThat_asserts :
  Ast.hint_annot_form_command ->
  Form.form * Form.form list -> Form.form * Form.form list
(** [sp_NoteThat c f] computes the postcondition for the [NoteThat c]
    operation under precondition [f]: [\{ f \} noteThat x \{ f \}]. *)

val sp_Assume_asserts :
  Ast.annot_form_command ->
  Form.form * Form.form list -> Form.form * Form.form list
(** [sp_Assume ac f] computes the postcondition for the [Assume] operation
    under precondition [f]: [\{ f \} assume h \{ f \}]. *)

val sp_Split_asserts :
  Ast.annot_form_command ->
  Form.form * Form.form list -> Form.form * Form.form list
(** [sp_Split s f] computes the postcondition for the [Split s] operation
    under precondition [f]: [\{ f \} split h \{ f \}]. *)

val sp_Havoc_asserts :
  Ast.havoc_command ->
  Form.form * Form.form list -> Form.form * Form.form list
(** [sp_Havoc hc f] computes the postcondition for the [Havoc hc] operation
    under precondition [f]: [\{ f \} havoc x_1, \dots, x_k suchThat c_1,
    \dots, c_n \{ c_i ; EX x_i. c_j ; f \}]. *)

val sp_ProcCall_asserts :
  Ast.proc_call -> Form.form * Form.form list -> Form.form * Form.form list
(** At that point, procedure calls should be desugared, so [sp_ProcCall pc
    f] returns [Failure "LoopInvariantInference: ProcCall should be
    desugared.\n"]. *)

val sp_bc_asserts :
  Form.form * Form.form list ->
  Ast.basic_command -> Form.form * Form.form list
(** It checks that strongest postcondition imply all assertions and require
    existence of intermediate values *)

val sp_noloops :
  Form.form * Form.form list -> Ast.command -> Form.form * Form.form list
(** Strongest postcondition of straight line code.  Returns the strongest
    postcondition and a list of assertions. *)
