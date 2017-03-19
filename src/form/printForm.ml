(** Printing {!Form} formulas to strings into
    representation understood by Isabelle. *)

open Form
open TypeVars

let concise = ref false
let xsymbols = ref false

let nullConstName = "null"

let p s = "(" ^ s ^ ")" 

(* ------------------------- *)
(* Added by Alexander Malkis *)

(* Returns true iff a formula has no subformulas except itself and can be written as a single identifier *)
let is_noncompound_form = function
    Var _ -> true
  | Const _ -> true
  | _ -> false

(* Returns true iff a type is simple *)
let is_noncompound_type = function
    TypeUniverse -> true
  | TypeVar _ -> true
  | TypeApp (t,[]) -> true
  | _ -> false

(* concatenate two strings, saving spaces when expressions are short. Throw out
spaces between
alphanumerical notalphanumerical 
notalphanumerical alphanumerical
anything (
) anything 
anything {
} anything
anything [
] anything 
 *)
let concat_saving_spaces (s1:string) (s2:string) :string =
  let (trimmed_s1,oc1)=Util.right_trim s1 in
  let (trimmed_s2,oc2)=Util.left_trim s2 in
  (match oc1 with
     None -> trimmed_s2
   | Some c1 ->
       (match oc2 with
          None -> trimmed_s1
        | Some c2 -> 
           (if ((Util.isalnum_ c1) && not (Util.isalnum_ c2))
            || ((not (Util.isalnum_ c1)) && (Util.isalnum_ c2))
            || (Util.is_left_paren c2)
            || (Util.is_right_paren c1)
            then (trimmed_s1^trimmed_s2) else (trimmed_s1^" "^trimmed_s2)
           )
       )
  )
(* ------------------------- *)

let wr_int = function
  | Const (IntConst i) -> Printf.sprintf "%d" i
  | _ -> failwith "vcprint.isa_form: non-constant cardinality constraint"

let isabelle_ident s = 
  Util.replace_dot_with_uscore s

let rec wr_form_list op fs = p (wr_form_list1 op fs)

and infx f1 op f2 = p (wr_form f1 ^ op ^ wr_form f2)

(* added a space-saving version: Alexander Malkis *)
and short_infx_form f1 op f2 :string = 
  let s1 = wr_form f1 in
  let s2 = wr_form f2 in
  if (is_noncompound_form f1) && (is_noncompound_form f2) then
    p (concat_saving_spaces s1 (concat_saving_spaces op s2))
  else p (s1^op^s2)

and prefx op f1 f2 = p (op ^ " " ^ wr_form f1 ^ " " ^ wr_form f2)

and wr_binding (v,t) =
  (let v_s = isabelle_ident v in 
     match t with
       | TypeUniverse -> v_s
       | _ -> 
	   if !concise then v_s 
	   else p (v_s ^ "::" ^ wr_type t))

and wr_bindings vts = String.concat " " (List.map wr_binding vts)

and wr_tuple vts = 
  "(" ^ String.concat ", " (List.map wr_binding vts) ^ ")"

and wr_binder binder vts f = 
  p (binder ^ " " ^ wr_bindings vts ^ ". " ^ wr_form f)

(* let (v::t) = e in f *)
and wr_let1 e (v,t) f =
  "let " ^ wr_binding (v,t) ^ " = " ^ wr_form e ^ " in " ^
    wr_form f

and wr_let e (v,t) f = p (wr_let1 e (v,t) f) 

(* Added by Alexander Malkis *)
(* concatenate types saving spaces *)
and short_infx_type t1 op t2 =
  let s1 = wr_type t1 in
  let s2 = wr_type t2 in
  if (is_noncompound_type t1) && (is_noncompound_type t2) then
    p (concat_saving_spaces s1 (concat_saving_spaces op s2))
  else p (s1^op^s2)

(* added by Alexander Malkis *)
(* concatenate formula and type saving spaces *)
and short_infx_form_type f1 op t2 =
  let s1 = wr_form f1 in
  let s2 = wr_type t2 in
  if (is_noncompound_form f1) && (is_noncompound_type t2) then
    p (concat_saving_spaces s1 (concat_saving_spaces op s2))
  else p (s1^op^s2)

(* changed by AM *)
(* Write bracketed type, trying to avoid unnecessary brackets *)
and wr_type_p = function
  | TypeApp(st,[]) -> wr_stype st
  | TypeApp(TypeArray,[it;et]) as t -> wr_type t
  | TypeFun(targs,res) as t -> wr_type t
  | TypeProd ts as t -> wr_type t
  | t -> p (wr_type t)

(* added by AM *)
(* Write a (possibly long-curried) function type. *)
(* If all types are simple, formula can be written saving spaces. *)
and wr_fun_type targs tres =
  p (
    if (List.for_all is_noncompound_type targs) && (is_noncompound_type tres) then
      let printed_targs = List.map wr_type_p targs in
      List.fold_right (fun tp sofar -> concat_saving_spaces tp (concat_saving_spaces " => " sofar)) printed_targs (wr_type_p tres)
    else String.concat " => " (List.map wr_type_p (targs@[tres]))
  )

and wr_type = function
  | TypeUniverse -> "universe"
  | TypeVar id -> "'" ^ id
  | TypeApp(TypeArray,[it;et]) -> (* p (wr_type it ^ " => " ^ wr_type et) *)
      short_infx_type it " => " et
  | TypeApp(st,ts) -> 
      String.concat " " 
        (List.map wr_type_p ts @ [wr_stype st])
  | TypeFun(targs,tres) -> (* p (String.concat " => " (List.map wr_type_p (targs @ [tres]))) *)
      wr_fun_type targs tres
  | TypeProd ts -> p (String.concat " * " (List.map wr_type_p ts))

and wr_stype = function
  | TypeUnit -> "unit"
  | TypeInt -> "int"
  | TypeString -> "string"
  | TypeBool -> "bool"
  | TypeObject -> "obj"
  | TypeArray -> "array"
  | TypeSet -> "set"
  | TypeList -> "list"
  | TypeDefined s -> isabelle_ident s

(*
and wr_fun_type ts t1 = match ts with
  | [] -> wr_type t1
  | t2::ts2 -> wr_type t2 ^ " => " ^ wr_fun_type ts2 t1
*)

and wr_form = function
  | Const (BoolConst true) -> "True"
  | Const (BoolConst false) -> "False"
  | App(Const Not, [App(Const Eq,[f1;f2])]) -> (* infx f1 (if !xsymbols then " \\<noteq> " else " ~= ") f2 *)
      short_infx_form f1 (if !xsymbols then " \\<noteq> " else " ~= ") f2
  | App(Const Not, [App(Const Elem,[f1;f2])]) -> (* infx f1 (if !xsymbols then " \\<notin> " else " ~: ") f2 *)
      short_infx_form f1 (if !xsymbols then " \\<notin> " else " ~: ") f2
  | App(Const Not, [f]) -> p ("~" ^ wr_form f)
  | App(Const Or,fs) -> 
      if !xsymbols then wr_form_list " \\<or> " fs
      else wr_form_list " | " fs
  | App(Const And,fs) -> 
      if !xsymbols then wr_form_list " \\<and> " fs
      else wr_form_list " & " fs
  | App(Const MetaAnd,fs) -> "[|" ^ wr_form_list1 ";\n" fs ^ "|]"
  | App(Const Impl,[f1;f2]) -> (* infx f1 " --> " f2 *)
      short_infx_form f1 " --> " f2
  | App(Const MetaImpl,[f1;f2]) -> infx f1 " ==>\n    " f2
  | App(Const Iff,[f1;f2]) -> (* infx f1 " <-> " f2 *)
      short_infx_form f1 " <-> " f2
  | App(Const Ite,[f1;f2;f3]) -> p ("if " ^ wr_form f1 ^ " then " ^ wr_form f2 ^ " else " ^ wr_form f3)
  | App(Const Eq,[f1;f2]) -> (* infx f1 " = " f2 *)
      short_infx_form f1 " = " f2
  | App(Const MetaEq,[f1;f2]) -> (* infx f1 " == " f2 *)
      short_infx_form f1 " == " f2
  | Const EmptysetConst -> "{}"
  | App(Const FiniteSetConst, fs) -> "{" ^ wr_form_list1 ", " fs ^ "}"
  | App(Const Tuple, fs) -> "(" ^ wr_form_list1 ", " fs ^ ")"
  | App(Const Elem,[f1;f2]) -> (* infx f1 (if !xsymbols then " \\<in> " else " : ") f2 *)
      short_infx_form f1 (if !xsymbols then " \\<in> " else " : ") f2
  | App(Const Subseteq,[f1;f2]) -> (* infx f1 " \\<subseteq> " f2 *)
      short_infx_form f1 " \\<subseteq> " f2
  | App(Const Subset,[f1;f2]) -> (* infx f1 " \\<subset> " f2 *)
      short_infx_form f1 " \\<subset> " f2
  | App(Const Seteq,[f1;f2]) -> (* infx f1 " === " f2 *)
      short_infx_form f1 " === " f2
  | App(Const Cap,fs) ->
      wr_form_list (if !xsymbols then " \\<inter> " else " Int ") fs
  | App(Const Cup,fs) -> 
      wr_form_list (if !xsymbols then " \\<union> " else " Un ") fs
  | App(Const Diff,[f1;f2]) -> (* infx f1 " \\<setminus> " f2 *)
      short_infx_form f1 " \\<setminus> " f2
  | App(Const Disjoint,fs) -> "handleDisjoint"
  | App(Const Cardeq,[f1;k]) -> "cardeq" ^ wr_int k ^ " " ^ wr_form f1
  | App(Const Cardleq,[f1;k]) -> "cardleq" ^ wr_int k ^ " " ^ wr_form f1
  | App(Const Cardgeq,[f1;k]) -> "cardgeq" ^ wr_int k ^ " " ^ wr_form f1

  | App(Const ListLiteral, fs) -> "[" ^ wr_form_list1 ", " fs ^ "]"

  | Const (IntConst k) -> Printf.sprintf "%d" k
  | Const (StringConst s) -> "''" ^ s ^ "''"
  | App(Const Lt,[f1;f2]) -> prefx "intless" f1 f2
  | App(Const LtEq,[f1;f2]) -> (* infx f1 " <= " f2 *)
      short_infx_form f1 " <= " f2
  | App(Const Gt,[f1;f2]) -> wr_form (App(Const Lt,[f2;f1]))
  | App(Const GtEq,[f1;f2]) -> wr_form (App(Const LtEq,[f2;f1]))

  | App(Const UMinus,[f]) -> p ("-" ^ wr_form f)
  | App(Const Plus,[f1;f2]) -> prefx "intplus" f1 f2
  | App(Const Minus,[f1;f2]) -> (* infx f1 " - " f2 *)
      short_infx_form f1 " - " f2
  | App(Const Mult,[f1;f2]) -> prefx "inttimes" f1 f2
  | App(Const Div,[f1;f2]) -> (* infx f1 " div " f2 *)
      short_infx_form f1 " div " f2
  | App(Const Mod,[f1;f2]) -> (* infx f1 " mod " f2 *)
      short_infx_form f1 " mod " f2
  | App(Const Rimage,[f1;f2]) -> (* infx f1 " `` " f2 *)
      short_infx_form f1 " `` " f2
  | App(Const FieldRead,[f1;f2]) when !concise ->
      wr_form_list " " [f1;f2]
  | App(Const FieldWrite,[f1;f2;f3]) when !concise ->
      p (wr_form f1 ^ "(" ^ wr_form f2 ^ " := " ^ wr_form f3 ^ ")")
  | App(Const Let,[f1;Binder(Lambda,[(v,t)],f2)]) -> 
      wr_let f1 (v,t) f2
        (* | App(Const Comment,[Var c;f]) -> " (* " ^ c ^ " *) " ^ wr_form f *)
  | App(Const Comment,[Const (StringConst s);f]) -> 
      p ("comment ''" ^ s ^ "'' " ^ wr_form f)
  | Const NullConst -> nullConstName
  | Const c -> Form.string_of_const c 

  | Var v -> isabelle_ident v
  | Binder(Forall,vts,f1) -> 
      wr_binder (if !xsymbols then "\\<forall>" else "ALL") vts f1
  | Binder(Exists,vts,f1) -> 
      wr_binder (if !xsymbols then "\\<exists>" else "EX") vts f1
  | Binder(Lambda,vts,f1) -> 
      wr_binder (if !xsymbols then "\\<lambda>" else "%") vts f1
  | Binder(Comprehension,[(v,t)],f1) ->
      (* Alas, also printing a type would lead to a formula that is currently not parseable by Jahob. *)
      "{" ^ isabelle_ident v ^ ". " ^ wr_form f1 ^ "}"
  | Binder(Comprehension,vts,f1) -> 
      (* "{" ^ wr_binder "" vts  f1 ^ "}" *)
      "{(" ^ wr_form_list1 ", " (List.map (fun (v, ty) -> TypedForm (Var v, ty)) vts) ^ "). " 
      ^ wr_form f1 ^ "}"
  | TypedForm(TypedForm(f1,t1),t2) -> wr_form (TypedForm(f1,t2))
  | TypedForm(f,TypeUniverse) -> wr_form f
  | TypedForm(f1,t) -> 
      if ftv t=[] && (not !concise) then (* p (wr_form f1 ^ " :: " ^ wr_type t) *)
        short_infx_form_type f1 " :: " t
      else wr_form f1
  | App(f1,fs) -> wr_form_list " " (f1::fs)

and wr_form_list1 op l =
  String.concat op (List.map wr_form l)

let string_of_type (t : typeForm) : string = wr_type t  

let string_of_env (t : typeEnv) : string =
  "{|" ^ String.concat ", " (List.map wr_binding t) ^ "|}"

let string_of_typedef (td : typeDef) : string =
  let wr_param (p : string) = "'" ^ p in
  let wr_params (ps : string list) = match ps with
    | [] -> ""
    | _ -> "(" ^ String.concat ", " (List.map wr_param ps) ^ ")" in
  let wr_body (b : typeDefBody) = match b with
    | SumType _ -> "aSumType"
    | RecordType _ -> "aRecordType"
    | Synonym tf -> wr_type tf
  in
  "type " ^ wr_params td.typDefTypeVars ^ td.typDefName ^ " = " ^
    wr_body td.typDefBody

let string_of_form (f:form) = wr_form f

let short_string_of_form (f:form) = 
  let old_concise = !concise in
  let old_xsymbols = !xsymbols in
    concise := true;
    xsymbols := true;
    let res = string_of_form f in
      concise := old_concise;
      xsymbols := old_xsymbols;
      res

let quoted_form f = "\"" ^ string_of_form f ^ "\""

let print_form f = print_endline (!Common.padding_string ^ string_of_form f)
let print_type ty = print_endline (!Common.padding_string ^ string_of_type ty)

(*
let isabelle_input (mod_name:string) (proof:string) (sq:string) =
  "theory vc = " ^ mod_name ^ ":\n" ^
   "lemma \"" ^ sq ^ "\"\n" ^ proof ^ "\nend\n"
*)

