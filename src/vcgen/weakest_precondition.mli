(** Weakest precondition path *)

val choose : Ast.specvar_def list -> Form.ident list -> Form.form -> Form.form
(** [choose defs ids f] conjoins the definition list [defs] depending only
    on variables from [ids] to the formula [form] with substitutions of the
    variables used in definitions *)

val choose_assign : Ast.specvar_def list ->
    Form.ident -> Form.form -> Form.form -> Form.form
(** Same as choose but for an assignment:
    \{ f[e/x] /\ x = e \} x := e \{ f \} *)

val wp_alloc : Ast.program -> (Form.ident * Form.form) list ->
    Form.ident -> Form.ident -> Form.form -> Form.form
(** [wp_alloc prog defs id ty f] computes the precondition of [(Alloc ac)]
    under postcondition [f]: [\{ \} id := new ty () \{ f \}] *)

val wp_array_alloc : Ast.program -> (Form.ident * Form.form) list ->
    Form.ident -> Form.form list -> Form.form -> Form.form
(** [wp_array_alloc prog defs id ty f] computes the precondition of [(Alloc
    ac)] under postcondition [f]: [\{ \} id := new ty () \{ f \}] *)

val havoc : (Form.ident * Form.form) list ->
    Form.form list -> Form.form -> Form.form

val mk_obligation : Ast.program -> Ast.impl_module ->
    (Form.ident * Form.form) list -> Form.ident list ->
    Common.source_pos -> Form.form * string -> Form.obligation

val weakest_precondition : Ast.program -> Ast.impl_module -> Ast.proc_def ->
    Form.form -> Ast.command option -> bool -> (Form.ident * Form.form) list ->
    Ast.command -> Form.form -> Form.form * (Form.form * string) list

val remove_old : Form.form -> Form.form
(** Rename all instances of (old x) into x for all x. *)

val wp_proc : Ast.program -> Ast.impl_module -> Ast.proc_def ->
    Ast.proc_header -> Ast.specvar_def list ->
    Ast.command option -> bool -> Form.obligation list
