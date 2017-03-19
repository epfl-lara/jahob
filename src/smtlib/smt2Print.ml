(** Facilities for converting formulas and strings to the SMTLIB2 standard. *)

open Form

(** [identifier_into_SMTLIB2_symbol id]
    converts the identifier into a symbol understood by SMTLIB 2. *)
let identifier_for_SMTLIB2 : string->string=
  let backslash_regexp = Str.regexp_string "\\" in
  let dollar_regexp = Str.regexp_string "$" in
  let underscore_regexp = Str.regexp_string "_" in
  let greater_regexp = Str.regexp_string ">" in
  let less_regexp = Str.regexp_string "<" in
  let star_regexp = Str.regexp_string "*" in
  let dash_regexp = Str.regexp_string "-" in
  fun id ->
    let s1 = Str.global_replace backslash_regexp "\\\\" id in
    let s2 = Str.global_replace dollar_regexp "\\$" s1 in
    let s3 = Str.global_replace underscore_regexp "\\_" s2 in
    let s4 = Str.global_replace greater_regexp "\\>" s3 in
    let s5 = Str.global_replace less_regexp "\\<" s4 in
    let s6 = Str.global_replace star_regexp "\\*" s5 in
    Str.global_replace dash_regexp "\\-" s6

(** [simpleType_to_SMTLIB2_symbol ty] *)
let simpleType_to_SMTLIB2_symbol : simpleType->string = function
      TypeUnit -> "Unit"
    | TypeInt -> "Int"
    | TypeString -> "String"
    | TypeBool -> "Bool"
    | TypeObject -> "Obj"
    | TypeArray -> "Array"
    | TypeSet -> "Set"
    | TypeList -> "List"
    | TypeDefined s -> identifier_for_SMTLIB2 s

(** [bracket_for_SMTLIB2 s] returns a bracketed form of s. *)
let rec bracket_for_SMTLIB2 (s:string): string = "<"^s^">"

and
(** [short_infx_type_to_SMTLIB2_symbol ty1 op ty2]
    concatenates ty1 and ty2 with op, saving brackets. *)
  short_infx_type_to_SMTLIB2_symbol (ty1:typeForm) (op:string) (ty2:typeForm) =
  let s1 = type_to_SMTLIB2_symbol ty1 in
  let s2 = type_to_SMTLIB2_symbol ty2 in
  bracket_for_SMTLIB2 (s1^op^s2)

and
(** [type_to_SMTLIB2_symbol_bracketed ty]
    creates an identifier for the type ty in brackets, trying to avoid unnecessary brackets. *) 
  type_to_bracketed_SMTLIB2_symbol : typeForm -> string = function
      TypeApp(st,[]) -> simpleType_to_SMTLIB2_symbol st
    | TypeApp(TypeArray,[it;et]) as t -> type_to_SMTLIB2_symbol t
    | TypeFun(targs,res) as t -> type_to_SMTLIB2_symbol t
    | TypeProd ts as t -> type_to_SMTLIB2_symbol t
    | t -> bracket_for_SMTLIB2 (type_to_SMTLIB2_symbol t)

and
(** [type_to_SMTLIB2_symbol ty]
    creates an identifier for the type ty. *)
  type_to_SMTLIB2_symbol :typeForm->string = function
      TypeUniverse -> "universe"
    | TypeVar id -> "$"^(identifier_for_SMTLIB2 id)
    | TypeApp(TypeArray,[it;et]) -> short_infx_type_to_SMTLIB2_symbol it "-" et
    | TypeApp(st,ts) -> String.concat "_" (List.map type_to_bracketed_SMTLIB2_symbol ts @ [simpleType_to_SMTLIB2_symbol st])
    | TypeFun(targs,tres) -> fun_type_to_SMTLIB2_symbol targs tres
    | TypeProd ts -> bracket_for_SMTLIB2 (String.concat "*" (List.map type_to_bracketed_SMTLIB2_symbol ts))

and
  (** [fun_type_to_SMTLIB2_symbol args res] returns the symbol for the function type from args to res *)
  fun_type_to_SMTLIB2_symbol (args:typeForm list) (res:typeForm) :string =
    bracket_for_SMTLIB2 (String.concat "-" (List.map type_to_bracketed_SMTLIB2_symbol (args@[res])))
