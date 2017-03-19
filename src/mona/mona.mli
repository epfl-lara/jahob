(** Interface to MONA. *)

(* val valid : TermRewrite.env -> Form.ident list -> Form.form -> bool *)
(** [Mona.valid env fields f] checks validity of Jahob formula [f] by
calling MONA. Formula [f] must be well-typed under typing environment
[env]. Validity is checked with respect to a graph type with backbone
fields [fields] and additional derived fields which may be provided
by [env] in terms of field constraints. *)

val prove_sequent : Common.options_t -> Form.typeEnv -> Form.sequent -> bool option
(** [Mona.prove_sequent s] try to prove validity of sequent [s] using MONA. *)
