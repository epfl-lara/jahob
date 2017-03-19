(** Joust pretty printer. *)

(*
   Joust: a Java lexer, parser, and pretty-printer written in OCaml
   Copyright (C) 2001  Eric C. Cooper <ecc@cmu.edu>
   Released under the GNU General Public License *)

val public_only : bool ref

val print_decl : Format.formatter -> Syntax.decl -> unit

val print_expr : Format.formatter -> Syntax.expr -> unit

val print_stmt : Format.formatter -> Syntax.stmt -> unit

val print: Format.formatter -> Syntax.compilation_unit -> unit
