(** Print {!Ast} defined types *)


(** {6 Handling indentation} *)


val pf : Form.form -> string
(** Short for [PrintForm.short_string_of_form]. *)

val qpf : Form.form -> string
(** Same as [pf] but encloses the formula between double quotes. *)

val pad_incr_length : int
(** The length of the padding increment. *)

val pad_increment : string
(** The default padding increment, a string of [pad_length] space
    characters. *)

val custom_incr_pad : string -> unit
(** Add the given string to the padding. Raise
    [invalid_arg "PrintAst.custom_incr_pad"] if the string length is not
    [pad_length]. *)

val incr_pad : unit -> unit
(** Increment the padding once using space characters. *)

val decr_pad : unit -> unit
(** Decrement the padding once. *)

val custom_indent : string -> ('a -> string) -> 'a -> string
(** Wrap a printing call with a padding increment before and decrement
    after. Watch printing side effects! You must freeze arguments evaluation
    if they use [Common.padding_string] or identation will be incorrect. *)

val indent : ('a -> string) -> 'a -> string
(** Alias for [custom_indent pad_increment]. Same remark about printing side
    effects. *)


(** {6 Printing basic commands} *)


val pr_skip : unit -> string
(** Print a 'skip' command. *)

val pr_var_assign : Ast.assign_command -> string
(** Print a variable assignment. *)

val pr_alloc : Ast.alloc_command -> string
(** Print a variable allocation. *)

val pr_array_alloc : Ast.array_alloc_command -> string
(** Print an array allocation. *)

val pr_annot_cmd : string -> Ast.annot_form_command -> string
(** Print an annoted command ('assume' or 'split'). *)

val pr_hint_annot_cmd : string -> Ast.hint_annot_form_command -> string
(** Print a hint annoted command ('assert' or 'noteThat'). *)

val pr_havoc : Ast.havoc_command -> string
(** Print a havoc command. *)

val pr_call : Ast.proc_call -> string
(** Print a procedure call. *)

val pr_hint : Ast.hint -> string
(** Print a hint command. *)

val pr_basic_cmd : Ast.basic_command -> string
(** Print a basic command. *)

val pr_basic_cell : Ast.basic_cell -> string
(** Print a basic command with its pre- and post-condiitons, if any. *)

val pr_seq : Ast.command list -> string
(** Print a sequence of commands. *)

val pr_choice : Ast.command list -> string
(** Print a 'choice' commands. *)

val pr_if : Ast.if_command -> string
(** Print an 'if then else' command. *)

val pr_loop : Ast.loop_command -> string
(** Print a loop. *)

val pr_return : Ast.return_command -> string
(** Print a 'return' command. *)

val pr_pickAny : Ast.pickAny_command -> string
(** Print a 'pickAny' command. *)

val pr_assuming : Ast.assuming_command -> string
(** Print an 'assuming' command. *)

val pr_command : Ast.command -> string
(** Print a command. *)


(** {6 Printing global program} *)


val pr_var_decl : Ast.var_decl -> string
(** Print variable declaration inside a single line (so no identation nor
    end of line ). *)

val pr_gvar_decl : Ast.var_decl -> string
(** Print global variable declaration, including var keyword. *)

val pr_contract : Ast.contract -> string
(** Print a procedure contract. *)

val pr_proc_header_line : Form.ident -> Ast.proc_header -> string
(** Print a procedure header. *)

val pr_proc_header : Form.ident -> Ast.proc_header -> string
(** Print a procedure header and contract. *)

val pr_vardef : Ast.specvar_def -> string
(** Print a variable specification. *)

val pr_vardefs : Ast.specvar_def list -> string
(** Print vardefs. *)

val pr_constdefs : Ast.specvar_def list -> string
(** Print constdefs. *)

val pr_proc_def : Form.ident -> Ast.proc_def -> string
(** Print procedure definition.*)

val pr_inv : Specs.invariant_desc -> string
(** Print an invariant. *)

val pr_invs : string -> Specs.invariant_desc list -> string
(** Print an invariant list. *)

val pr_owner : Form.ident option -> string
(** Print the owner of a method or variable. *)

val pr_impl : Ast.impl_module -> string
(** Print an implementation module. *)

val pr_spec_module : Ast.spec_module -> string
(** Print a specification module. *)

val pr_typeDef : Form.typeDef -> string
(** Print a type definition. *)

val pr_map : Ast.mapping -> string
(** Print a mapping. *)

val pr_program : Ast.program -> string
(** Print an entire program. *)

(** {6 Printing simplified (normalized) ast} *)

val spr_impl : Ast.impl_module -> string
(** Print a implementation module of the simplified program. *)

val simplified_program : Ast.program -> string
(** Print a simplified (normalized) program. *)
