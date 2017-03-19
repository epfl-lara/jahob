(* Printing {!Form} formulas to SMT-LIB format. *)

open Form
open FormUtil

(* This is a shorthand for printing debug messages for this module. *)
let debug_id : int = Debug.register_debug_module "SmtPrint"
let debug_msg : (string -> unit) = Debug.debug_msg debug_id
let debug_is_on () : bool = Debug.debug_is_on debug_id

(** Indent and add backslash in front of every left and right parenthesis. *)
let format_source (s : string) : string =
  Str.global_replace (Str.regexp "{") "\\{"
    (Str.global_replace (Str.regexp "}") "\\}"
       (Str.global_replace (Str.regexp "\n") "\n\t" s))

let string_of_simpletype (st : simpleType) : string =
  match st with
    | TypeUnit -> "Unit"
    | TypeInt -> "Int"
    | TypeString -> "String"
    | TypeBool -> "Bool"
    | TypeObject -> "Obj"
    | TypeSet -> "Set"
    | TypeList -> "List"
    | TypeArray -> "Obj" (* SMT-LIB Array is for integer arrays only *)
    | TypeDefined(i) -> i

let rec string_of_typeform (str : string) (tf : typeForm) : string =
  let strnew = if (not (str = "")) then (str ^ " ") else str in
    match tf with
      | TypeApp(st, []) -> 
	  strnew ^ (string_of_simpletype st)
      | TypeApp(st, tl) ->
	  List.fold_left string_of_typeform (strnew ^ (string_of_simpletype st)) tl
      | TypeFun(args, res) ->
	  List.fold_left string_of_typeform str (args @ [res])
      | TypeVar i -> strnew ^ i
      | TypeProd tys ->
	  List.fold_left string_of_typeform str tys
      | _ -> failwith 
	  ("string_of_typeform: Not yet implemented:\n" ^ 
	     (MlPrintForm.string_of_type tf))

let smt_ident (i : ident) : string =
  let nocarets = Str.global_replace (Str.regexp "\\^") "$" i in
  let rec replace_dots (s : string) : string =
    try
      let j = Str.search_forward (Str.regexp "\\.") s 0 in
	(Str.string_before s j) ^ 
	  replace_dots (String.capitalize (Str.string_after s (j + 1)))
    with Not_found -> s in
    String.uncapitalize (replace_dots nocarets)

let make_extrapreds (s : string) : string =
  let smt_trigger_lg = String.length smt_trigger in
  let pred =
    if smt_trigger_lg < String.length s 
    then String.sub s 0 (smt_trigger_lg)
    else ""
  in
  if pred = smt_trigger then ""
  else "  :extrapreds ((" ^ s ^ "))\n"

let make_extrafuns (s : string) : string =
  "  :extrafuns ((" ^ s ^ "))\n"

let smt_extras (env : typeEnv) : string =
  let rec get_sorts (tfl : typeForm list) (tf : typeForm) : (typeForm list) =
    match tf with
      | TypeApp(st0, tfl0) ->
	  let tf0 = TypeApp (st0, []) in
	    if (st0 = TypeInt || st0 = TypeSet || st0 = TypeArray ||
		(List.exists (fun (x) -> x = tf0) tfl)) then
	      List.fold_left get_sorts tfl tfl0
	    else
	      List.fold_left get_sorts (tf0 :: tfl) tfl0
      | TypeFun(args, ret) ->
	  get_sorts (List.fold_left get_sorts tfl args) ret
      | TypeProd tfl0 ->
	  List.fold_left get_sorts tfl tfl0
      | _ -> if (not (List.exists (fun(x) -> x = tf) tfl)) then (tf :: tfl) else tfl in
  let make_extrasorts (str : string) (tf : typeForm) : string =
    match tf with
      | TypeApp(TypeBool, []) -> str
      | _ -> str ^ "  :extrasorts (" ^ (string_of_typeform "" tf) ^ ")\n" in
  let extrasorts_list = snd (List.split env) in
  let extrasorts = List.fold_left make_extrasorts "" 
    (List.fold_left get_sorts [] extrasorts_list) in
  let func_and_pred_string ((id0, ty) : typedIdent) : string =
    let id = smt_ident id0 in
      match normalize_type ty with
	| TypeApp(TypeBool, []) -> make_extrapreds id
	| TypeApp(sta, []) -> 
	    make_extrafuns (id ^ " " ^ (string_of_simpletype sta))
	| TypeApp(TypeSet, TypeApp(sta, []) :: []) ->
	    make_extrapreds (id ^ " " ^ (string_of_simpletype sta))
	| TypeApp(TypeArray, [_; ret]) ->
	    make_extrafuns (id ^ " " ^ (string_of_simpletype TypeArray) ^ 
			      " " ^ (string_of_typeform "" ret))
	| TypeFun(args, TypeApp(TypeBool, [])) ->
	    make_extrapreds 
	      (id ^ " " ^ (List.fold_left string_of_typeform "" args))
	| TypeFun(args, TypeApp(TypeSet, [set_of])) ->
	    make_extrapreds 
	      (id ^ " " ^ (List.fold_left string_of_typeform "" args) ^ 
		 " " ^ (string_of_typeform "" set_of))
	| TypeFun(args, ret) ->
	    make_extrafuns 
	      (id ^ " " ^ (List.fold_left string_of_typeform "" args) ^ 
		 " " ^ (string_of_typeform "" ret))
	| TypeVar i ->
	    make_extrafuns (id ^ " " ^ i)
	| _ -> 
	    failwith ("smt_extras: " ^ id ^ " " ^ (PrintForm.string_of_type ty)) in
  let other_extras = List.map func_and_pred_string env in
  let other_extras = List.fold_left (fun x y -> x ^ y) "" other_extras in
    extrasorts ^ other_extras


let rec smt_string (f : form) : string =
  let check_type ((_, ty) : typedIdent) : unit =
    match ty with
      | TypeVar _ | TypeApp(_, []) -> ()
      | _ -> failwith ("Formulas in smtlib cannot have quantification over type: " ^ 
			 (PrintForm.string_of_type ty) ^ "\n")
  in
  match f with
    | Var i -> smt_ident i
    | Const Not -> "not"
    | Const Or -> "or"
    | Const And -> "and"
    | Const Ite -> "ite"
    | Const Iff -> "iff"
    | Const UMinus -> "~"
    | Const Mult -> "*"
    | Const Div -> "/"
    | Const Mod -> "mod"
    | Const (IntConst i) -> 
	if i < 0 then Printf.sprintf ("(~ %d)") (- i) else string_of_int i
    | Const c -> Form.string_of_const c
    | App(Const Tuple, fs) -> smt_string_list fs
    | App(Var rtrancl, [p; t1; t2]) when rtrancl = str_rtrancl ->
	let st1 = smt_string t1 in
	let st2 = smt_string t2 in
	let sp = smt_string p in
	Printf.sprintf "(or (= %s %s) (%s %s %s : transclose))" st1 st2 sp st1 st2
    | App(Const fop, fs) when (fop = FieldRead || fop = FieldWrite) ->
	"(" ^ (smt_string_list fs) ^ ")"
    | App(Const ArrayRead, [f0; f1; f2]) ->
	"(arrayRead " ^ smt_string f0 ^ " " ^ smt_string f1 ^ " " ^ smt_string f2 ^ ")"
    | App(Const Elem, _) ->
	failwith ("smt_string did not expect: " ^ (PrintForm.string_of_form f) ^ "\n")
    | App(App(f0, fs0), fs1) ->
	smt_string (App(f0, fs0 @ fs1))
    | App(f1, fs) -> "(" ^ (smt_string f1) ^ " " ^ (smt_string_list fs) ^ ")"
    | Binder(Forall, til, f1) ->
	List.iter check_type til;
	( match f1 with
	    | App(Var trigger, f_lst)
	    | App(Const Not, [App(Var trigger, f_lst)])
	      when is_trigger trigger -> 
	      debug_msg ("found smt_trigger ...\n" ^ PrintForm.string_of_form f1 
			 ^ " \n" ^ MlPrintForm.string_of_form f1 ^ "\n" ) ;
		  let rec build_trigger_str tr_lst =
		    (  match tr_lst with
		      | [] -> ""
		      | trg :: flst -> ( smt_string trg ^ (build_trigger_str flst)  ) )
		  in
		  let f, trigger_str =
		    match f_lst with
		    | f :: trg -> 
		      let trigger_str = ":pat { " ^ (build_trigger_str trg) ^ " } " in
		      f, trigger_str
		    | [] ->  failwith ("SmtPrint.smt_string: empty trigger")
		  in
		  (match f1 with
		  | App (Const Not, _) ->
		      "(forall " ^ (smt_typedident_list til) 
		      ^ " " ^ (smt_string (mk_not f)) ^ " " ^ trigger_str  ^ ")"
		  | _ -> 
		      "(forall " ^ (smt_typedident_list til) 
		      ^ " " ^ (smt_string f) ^ " " ^ trigger_str  ^ ")")
	    | _ -> "(forall " ^ (smt_typedident_list til) ^ " " ^ (smt_string f1) ^ ")"
	)	  	
    | Binder(Exists, til, f1) ->
	List.iter check_type til;
	"(exists " ^ (smt_typedident_list til) ^ " " ^ (smt_string f1) ^ ")"
    | _ -> 
	print_string ("\n" ^ (MlPrintForm.string_of_form f) ^ "\n");
	failwith ("smt_string: Can't convert " ^ (PrintForm.string_of_form f))
and smt_string_list (fs : form list) : string =
  match fs with
    | [] -> ""
    | [f0] -> smt_string f0
    | f0 :: f1 -> (smt_string f0) ^ " " ^ (smt_string_list f1)
and smt_typedident_list (til : typedIdent list) : string =
  match til with
    | [] -> ""
    | [ti0] -> smt_typedident ti0
    | ti0 :: ti1 -> (smt_typedident ti0) ^ " " ^ (smt_typedident_list ti1)
and smt_typedident (i, t) : string =
  "(" ^ (smt_ident i) ^ " " ^ (string_of_typeform "" t) ^ ")"

(** This pass is no longer in use, because it has been subsumed by
    rewrite_sets. If you want to use this pass, you must run it on
    typed form, because this translation needs the type of the set
    elements. *)
(*
let rec translate_set_exprs (f : form) : (form) =
  match f with
    | Var _ -> f
    | Const _ -> f
    | App(Const Eq, [TypedForm (f0, TypeApp (TypeSet, [t0])); f1])
    | App(Const Eq, [f0; TypedForm (f1, TypeApp (TypeSet, [t0]))]) ->
	(match f0 with
	   | (Const EmptysetConst) ->
	       let fv = fresh_smt_var "setElem" in
	       let f2 = App (Const Elem, [(Var fv); f1]) in
	       let f3 = Binder (Forall, [(fv, t0)], (App ((Const Not), [f2]))) in
		 translate_set_exprs f3
	   | _ ->
	       let fv = fresh_smt_var "setElem" in
	       let f2 = App (Const Elem, [(Var fv); f0]) in
	       let f3 = App (Const Elem, [(Var fv); f1]) in
	       let f4 = Binder (Forall, [(fv, t0)], (App ((Const Iff), [f2; f3]))) in
		 translate_set_exprs f4)
    | App(Const Comment, [f0; f1]) -> translate_set_exprs f1 (* remove comments *)
    | App(f0, fs) ->
	let fs0 = List.map translate_set_exprs fs in
	  App((translate_set_exprs f0), fs0)
    | Binder (b0, t0, f0) -> Binder(b0, t0, (translate_set_exprs f0))
    | TypedForm (f0, t0) -> translate_set_exprs f0
*)

let convert_to_smt_string 
    (s : sequent) (name : string) (env : typeEnv) (fs : form list) (goal : form) : string =
  let smt_header_string 
      (s : sequent) (name : string) (logic : string) : string = 
    "(benchmark " ^ name ^ "\n" ^
      "  :source {\n" ^ 
      "\t" ^ (format_source (string_of_sequent s)) ^ "\n" ^
      "   }\n" ^
      "  :logic " ^ logic ^ "\n" in
  let header = smt_header_string s name "AUFLIA" in
  let extras = smt_extras env in
  let smt_assumptions (str : string) (f : form) : string =
    let str0 = smt_string f in
    if (not (str0 = "")) then
      str ^ "  :assumption " ^ str0 ^ "\n"
    else str in
  let assumptions = List.fold_left smt_assumptions "" fs in
  let formula = "  :formula    " ^ (smt_string goal) ^ "\n" in
  let res=(header ^ "\n" ^ extras ^ "\n" ^ assumptions ^ "\n" ^ formula ^ 
      "\n  :status     unknown\n)") in
  (debug_msg ("convert_to_smt_string finished with\n"^res^".\n");res)




