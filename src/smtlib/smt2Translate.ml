(* Translates Form to the subset of Form supported by SMT-LIB 2.0 *)

open Form
open LargeFormUtils

(** [smt2_reserved_words_list],
    [smt2_reserved_words_set]
    are the list and the set of the identifiers that cannot be a variable name, either by the definition of the SMTLIB 2.0 standard or by the actual behaviour of the used solvers z3 3.3 and cvc3 2012-03-04. Notice that no such identifier is a Jahob pseudo constant. *)
let smt2_reserved_words_list = ["par";"NUMERAL";"DECIMAL";"STRING"; "_";"!";"as";"let";"forall";"exists";"set-logic";"set-option";"set-info";"declare-sort";"define-sort";"declare-fun";"define-fun";"push";"pop";"assert";"check-sat";"get-assertions";"get-proof";"get-unsat-core";"get-value";"get-assignment";"get-option";"get-info";"exit";"select"; "store"; "false";"true";"and";"or";"not";"Int"; "Bool"; "distinct";"ite"]
let smt2_reserved_words_set = List.fold_left (fun sofar word -> SetOfVars.add word sofar) SetOfVars.empty smt2_reserved_words_list

(* The words used for sets and cardinality. *)
let member_prefix = "memberOf_"
let sizeOfSupport_prefix = "sizeOfSupport_"
let sizeOfSupportIsExactlyConstant_prefix = "sizeOfSupportIsExactlyConstant_"
let sizeOfSupportIsAtMostConstant_prefix = "sizeOfSupportIsAtMostConstant_"
let sizeOfSupportIsAtLeastConstant_prefix = "sizeOfSupportIsAtLeastConstant_"
let represents_prefix ="represents_"
let isAFiniteSet_prefix = "isAFiniteSet_"
let emptySet_prefix = "emptySet_"
let universalSet_prefix = "universalSet_"
let disjoint_prefix  = "disjoint_"
let cardeq_prefix = "cardEq_"
let cardleq_prefix = "cardLEq_"
let cardgeq_prefix = "cardGEq_"
let union_prefix = "union_"
let intersection_prefix = "intersection_"
let difference_prefix = "diff_"
let subseteq_prefix = "subsetEq_"
let strictSubset_prefix = "strictSubset_"
let finiteSet_prefix = "finiteSet_"

(* All reserved words. *)
let all_reserved_words_set = smt2_reserved_words_set

(* Never start identifiers with the following words. *)
let newPrefixes_list = [member_prefix; sizeOfSupport_prefix; represents_prefix; isAFiniteSet_prefix; emptySet_prefix; universalSet_prefix; disjoint_prefix; cardeq_prefix; cardleq_prefix; cardgeq_prefix; union_prefix; intersection_prefix; difference_prefix; subseteq_prefix; strictSubset_prefix; finiteSet_prefix]
let newPrefixes_set = List.fold_left (fun sofar word -> SetOfVars.add word sofar) SetOfVars.empty newPrefixes_list

let rec sanitize_word_for_SMTLIB2 (word:ident) : ident option =
  if (SetOfVars.mem word all_reserved_words_set) || (SetOfVars.exists (fun keyword -> Util.string_starts_with_string word keyword) newPrefixes_set) then
    let new_word = Util.fresh_name word in
    match sanitize_word_for_SMTLIB2 new_word with
        None -> Some new_word
      | w -> w
  else None

(** [sanitize_sequent_for_SMTLIB2 env s]
    replaces variables whose names are keywords by fresh variables both in the sequent s and its type environment env.
    Returns a pair (env',s') where env' is the new type environment and s' is the new sequent. *)
let sanitize_sequent_for_SMTLIB2 (global_env:mapVarType) : sequent -> (mapVarType*sequent) =
  let (new_global_env, sbst) = MapOfVars.fold
    (fun var ty (sofar_env,sofar_subst) -> 
      match sanitize_word_for_SMTLIB2 var with
          None -> ((MapOfVars.add var ty sofar_env),sofar_subst)
        | Some new_var -> ((MapOfVars.add new_var ty sofar_env),(MapOfVars.add var new_var sofar_subst)))
    global_env (MapOfVars.empty,MapOfVars.empty) in
  let rec sanitize_form sbst = function
      (Var v) as f -> 
        (try let new_v = MapOfVars.find v sbst in ((Var new_v),sbst)
         with Not_found -> 
           (match sanitize_word_for_SMTLIB2 v with
               None -> (f,sbst)
             | Some new_v -> ((Var new_v),(MapOfVars.add v new_v sbst))))
    | App(f0,fl) -> 
        let (new_f0,sbst_after_f0) = sanitize_form sbst f0 in
        let (new_fl,sbst_after_f0_fl) = sanitize_form_list sbst_after_f0 fl in
        ((App(new_f0,new_fl)),sbst_after_f0_fl)
    | Binder(b,tvl,ff) -> 
        let (new_subst,new_tvl) = sanitize_typed_varlist sbst tvl in
        let (new_ff,new_subst) = sanitize_form new_subst ff in
        ((Binder(b,new_tvl,new_ff)),new_subst)
    | TypedForm(f,tf) -> 
        let (new_f,new_subst) = sanitize_form sbst f in ((TypedForm(new_f,tf)),new_subst)
    | f -> (f,sbst)
  and sanitize_form_list sbst fl = 
    List.fold_right (fun frm (sofar_fl,sofar_sbst) -> let (new_f,new_sbst) = sanitize_form sofar_sbst frm in ((new_f::sofar_fl),new_sbst)) fl ([],sbst)
  and sanitize_typed_varlist sbst til = 
    List.fold_right (fun (v,ty) (sofar_sbst,sofar_list) -> 
      match sanitize_word_for_SMTLIB2 v with 
          None -> (sofar_sbst,((v,ty)::sofar_list))
	| Some new_var -> ((MapOfVars.add v new_var sofar_sbst),((new_var,ty)::sofar_list)))
      til (sbst,[]) in
  fun (asms,succ) ->
    let (new_asms,sbst_after_asms) = sanitize_form_list sbst asms in
    let (new_succ,_) = sanitize_form sbst_after_asms succ in
  (new_global_env, (new_asms,new_succ))

module Int = struct
	type t = int
	let compare = compare
end

module MapOfInts = Map.Make(Int)
type mapIntIdent = ident MapOfInts.t

(** [typeInformation] 
    stores information about a finite type. Parts of information may be missing.
    - emptyset_symb is the empty set symbol,
    - universalset_symb is the universal set symbol,
    - disjoint_symb maps the pairwise disjointness test over n sets to a symbol dependent on n,
    - size_of_support_symb stores the name of the function defining the size of support of the map from the type to booleans,
    - size_of_support_constraint_present shows whether the constraints for the size-of-support should be generated or not,
    - size_of_support_is_exactly_constant stores the name of the function that takes a set and an integer and answers whether the set has the cardinality equal to that integer,
    - size_of_support_is_at_least_constant stores the name of the function that takes a set and an integer and answers whether the set has the cardinality => to that integer,
    - size_of_support_is_at_most_constant stores the name of the function that takes a set and an integer and answers whether the set has the cardinality <= to that integer,
    - union_symb maps the union over n sets to a symbol dependent on n,
    - intersection_symb maps the intersection over n sets to a symbol dependent on n,
    - difference_symb maps sets A and B to their difference A\B,
    - subseteq_symb is the symbol for the subset inclusion,
    - strictSubset_symb is the symbol for the strict subset inclusion,
    - finiteSet_symb maps a natural number n to the symbol for finite sets of cardinality n,
    - member_symb is the symbol for the membership,
    - nonMember_symb is the symbol for the negation of the membership,
    - singleton_symb is the symbol for the singleton function,
*)

type typeInformation = {
    emptyset_symb: ident option;
    universalset_symb: ident option;
    disjoint_symb: mapIntIdent;
    size_of_support_symb: ident option;
    size_of_support_constraint_present: bool;
    size_of_support_is_exactly_constant: ident option;
    size_of_support_is_at_least_constant: ident option;
    size_of_support_is_at_most_constant: ident option;
    union_symb: mapIntIdent;
    intersection_symb: mapIntIdent;
    difference_symb: ident option;
    subseteq_symb: ident option;
    strictSubset_symb: ident option;
    finiteSet_symb: mapIntIdent;
    member_symb: ident option;
    nonMember_symb: ident option;
    singleton_symb: ident option;
}

(** [size_of_support_symb ty type_info]
    returns the symbol for the size-of-support of type=>bool. Takes the value from type_info, if it is there, or generates it, if not. Returns (symbol, updated type information). *)
(* not needed *)
(*
let size_of_support_symb_of_objset  (ty:typeForm) (type_info : typeInformation) : (ident*typeInformation) = 
    match type_info.size_of_support_symb with 
	None -> 
	  let s = sizeOfSupport_prefix^(Smt2Print.type_to_SMTLIB2_symbol (FormUtil.mk_set_type ty)) in
          let s = match sanitize_word_for_SMTLIB2 s with None -> s | Some x -> x in
	  (s, { type_info with size_of_support_symb = Some s})
      | Some s -> (s, type_info)
*)

(** [predicate_on_objects_type]
    is the type of the object sets as predicates. *)
let predicate_on_objects_type = FormUtil.mk_fun_type [FormUtil.mk_object_type] FormUtil.mk_bool_type

(** [axiomatize_size_of_objset_support typed_size_of_support_var type_info]
    returns formulas partially describing the size of support of object sets, adding those to type information.
    Returns the pair (the set of new formulas, the updated type information map).
 *)
(*
let axiomatize_size_of_objset_support : form -> typeInformation -> (setOfForms*typeInformation) =
  let var_name = Util.fresh_name "S" in
  let new_var = FormUtil.mk_var var_name in
  let typed_v = FormUtil.mk_typedform (new_var,predicate_on_objects_type) in
  fun (typed_var_size_of_support:form) (type_info:typeInformation) ->
    let zero_frm =Const (IntConst 0) in
    let size_of_support_nonneg = App((Const GtEq),[App(typed_var_size_of_support,[typed_v]);zero_frm]) in
    let form1 = FormUtil.mk_forall (var_name,predicate_on_objects_type,size_of_support_nonneg) in
    let (emptyset_str,type_info1) = 
      (match type_info.emptyset_symb with 
           Some s -> (s,type_info)
         | None -> 
             let s = Util.fresh_name (emptySet_prefix^(FormUtil.objset_str)) in
             (s,{type_info with emptyset_symb = Some s})) in
    let typed_empty_frm = FormUtil.mk_typedform ((FormUtil.mk_var emptyset_str),predicate_on_objects_type) in
    let v_is_empty = FormUtil.mk_eq (typed_v,typed_empty_frm) in
    let v_size0 = FormUtil.mk_eq ((App(typed_var_size_of_support,[typed_v])),zero_frm) in
    let empty_iff_size0 = FormUtil.mk_iff (v_is_empty,v_size0) in
    let form2 = FormUtil.mk_forall (var_name,predicate_on_objects_type,empty_iff_size0) in
    let axioms = SetOfForms.add form1 (SetOfForms.singleton form2) in
    let type_info2 = { type_info1 with fun_constraint = (SetOfForms.union type_info1.fun_constraint axioms) } in
    (axioms,type_info2)
*)

(** [size_of_support_of_objset_type]
    is the type of the cardinality operator as size-of-support. *)
let size_of_support_of_objset_type = FormUtil.mk_fun_type [predicate_on_objects_type] FormUtil.mk_int_type

(** [member_obj_objset_type]
    is the type of the membership relation between objects and sets of objects as application. *)
let member_obj_objset_type = FormUtil.mk_fun_type [FormUtil.mk_object_type;predicate_on_objects_type] FormUtil.mk_bool_type

(** [test_on_two_object_predicates_type]
    is the type of operations like set inclusion between a pair of sets of objects as between two predicates on objects. *)
let test_on_two_object_predicates_type = FormUtil.mk_fun_type [predicate_on_objects_type;predicate_on_objects_type] FormUtil.mk_bool_type

(** [size_of_support_of_objset_is_constant_type]
    is the type of the function that checks whether the size of support of a predicate is exactly, less-than-or-equal-to, or greater-than-or-equal-to a constant. *)
let size_of_support_of_objset_is_constant_type = FormUtil.mk_fun_type [predicate_on_objects_type;(FormUtil.mk_int_type)] (FormUtil.mk_bool_type)

(** [operator_on_object_predicates_type]
    is the type of operations taking two object predicates and returning an object predicate. *)
let operator_on_object_predicates_type = FormUtil.mk_fun_type [predicate_on_objects_type;predicate_on_objects_type] predicate_on_objects_type

(* The result of type conversion. *)
type typeConvertResult =
    TypeExactlyConverted of typeForm
  | NonObjSetTypesPresent of typeForm
  | NoTypeConversionNeeded

type typeListConvertResult =
    TypeListExactlyConverted of (typeForm list)
  | TypeListWithNonObjSet of (typeForm list)
  | NoTypeListConversionNeeded

(** [try_get_rid_of_sets_in_type ty]
    replaces object sets by (obj=>bool) in the type ty, returning 
      - TypeExactlyConverted new_ty in case convertion was exactly performed,
      - NonObjSetTypesPresent new_ty, if, despite a potential partial conversion, other set types are still present there,
      - NoTypeConvertionNeeded, if the type does not contain set types. *)
let rec try_get_rid_of_sets_in_type (ty: typeForm) : typeConvertResult =
  match ty with
      TypeUniverse | TypeVar _ -> NoTypeConversionNeeded
    | TypeApp(TypeSet,[TypeApp(TypeObject,[])]) -> TypeExactlyConverted predicate_on_objects_type
    | TypeApp(TypeSet,_) -> NonObjSetTypesPresent ty
    | TypeApp(st,lst) ->
        let (new_lst,approximation_needed,anything_changed) = try_get_rid_of_sets_in_type_aux lst in
	if approximation_needed then NonObjSetTypesPresent (TypeApp(st,new_lst))
	else if anything_changed then TypeExactlyConverted (TypeApp(st,new_lst))
	else NoTypeConversionNeeded
    | TypeFun(lst,res_ty) ->
        let (new_lst,approximation_needed,anything_changed) = try_get_rid_of_sets_in_type_aux lst in
	if approximation_needed then
	  match try_get_rid_of_sets_in_type res_ty with
	      TypeExactlyConverted new_res_ty
	    | NonObjSetTypesPresent new_res_ty -> NonObjSetTypesPresent (TypeFun(new_lst,new_res_ty))
	    | NoTypeConversionNeeded -> NonObjSetTypesPresent (TypeFun(new_lst,res_ty))
	else if anything_changed then
	  match try_get_rid_of_sets_in_type res_ty with
	      TypeExactlyConverted new_res_ty -> TypeExactlyConverted (TypeFun(new_lst,new_res_ty))
	    | NonObjSetTypesPresent new_res_ty -> NonObjSetTypesPresent (TypeFun(new_lst,new_res_ty))
	    | NoTypeConversionNeeded -> TypeExactlyConverted (TypeFun(new_lst,res_ty))
	else NoTypeConversionNeeded
    | TypeProd lst ->
        let (new_lst,approximation_needed,anything_changed) = try_get_rid_of_sets_in_type_aux lst in
	if approximation_needed then NonObjSetTypesPresent (TypeProd new_lst)
	else if anything_changed then TypeExactlyConverted (TypeProd new_lst)
	else NoTypeConversionNeeded
and
    (** [try_get_rid_of_sets_in_type_aux tlst]
	replaces object sets by (obj=>bool) in the the list of types lst, returning (res_lst,approx,changed), where
	- res_lst is the resulting list,
	- approx is true in case nonobject sets are left over,
	- changed is true if some conversions have indeed happened. *)
    try_get_rid_of_sets_in_type_aux (tlst : (typeForm list)) : ((typeForm list)*bool*bool) =
    List.fold_right 
      (fun elem_ty (sofar_lst,sofar_approximation_needed,sofar_changed) -> 
        match try_get_rid_of_sets_in_type elem_ty with
	    TypeExactlyConverted new_elem_ty -> ((new_elem_ty::sofar_lst),sofar_approximation_needed,true)
          | NonObjSetTypesPresent new_elem_ty -> ((new_elem_ty::sofar_lst),true,true)
	  | NoTypeConversionNeeded -> ((elem_ty::sofar_lst),sofar_approximation_needed,sofar_changed))
      tlst ([],false,false)

(** [try_get_rid_of_sets_in_type_list lst]
    replaces object sets by (obj=>bool) in the the list of types lst, returning 
      - TypeExactlyConverted new_lst in case convertion was exactly performed,
      - NonObjSetTypesPresent new_lst, if, despite a potential partial conversion, other set types are still present there,
      - NoTypeConvertionNeeded, if the type does not contain set types. *)
let try_get_rid_of_sets_in_type_list (lst: (typeForm list)) : typeListConvertResult =
  let (new_lst,approximation_needed,anything_changed) = try_get_rid_of_sets_in_type_aux lst in
  if approximation_needed then TypeListWithNonObjSet new_lst
  else if anything_changed then TypeListExactlyConverted new_lst
  else NoTypeListConversionNeeded

(* The result of conversion of terms. *)
(*
type termConvertResult = 
    TermExactlyConverted of (mapVarType*mapVarType*typeInformation*form)
  | TermNonObjSetsProbablyLeft of (mapVarType*mapVarType*typeInformation*form)
  | TermApproximationNeeded
  | NoTermConversionNeeded
*)
type termConversionResult = 
    TermExactlyConverted of (mapVarType*typeInformation*form)
  | TermNonObjSetsProbablyLeft of (mapVarType*typeInformation*form)
  | TermApproximationNeeded
  | NoTermConversionNeeded

(* The result of conversion of term lists. *)
(*
type termListConvertResult =
    TermListExactlyConverted of (mapVarType*mapVarType*typeInformation*(form list))
  | TermListNonObjSetsProbablyLeft of (mapVarType*mapVarType*typeInformation*(form list))
  | TermListApproximationNeeded
  | NoTermListConversionNeeded
*)
type termListConvertResult =
    TermListExactlyConverted of (mapVarType*typeInformation*(form list))
  | TermListNonObjSetsProbablyLeft of (mapVarType*typeInformation*(form list))
  | TermListApproximationNeeded
  | NoTermListConversionNeeded

(** [make_list_of_identical_items item n]
    creates a list of n identical items. *)
let make_list_of_identical_items (item:'a) : int -> ('a list) =
  let rec aux n = if n<=0 then [] else item::(aux (n-1)) in
  aux

(** [get_rid_of_sets_in_trm type_env type_info trm]
    recursiveley rewrites terms of the object set type in the term trm into predicates, noticing whether other sets are present, and possibly cancelling the conversion. The constants representing functions accepting or returning object sets are replaced by fixed-named variables with a higher-order function type, the constants representing object sets are replaced by fixed-name predicates. The map type_env binds all variables to their current types. type_info contains information about what fixed-named functions and predicates are already needed, as well as what axioms are already needed.
    If the term could be updated and no other set terms are left, returns
    TermExactlyConverted(changes_of_type_env,updated_type_info,new_term), where changes_of_type_env say what other variables should also get their type rewritten, updated_type_info is the updated information about object sets represented as maps obj=>bool, new_trm is the rewritten term.
    If the term could be updated such that no object sets are left but other sets might have been left, returns
    TermNonObjSetsProbablyLeft(changes_of_type_env,updated_type_info,new_term), where changes_of_type_env say what other variables should also get their type rewritten, updated_type_info is the updated information about object sets represented as maps obj=>bool, new_trm is the rewritten term.
    If the term could not be updated, but has to be abstracted away, returns TermApproximationNeeded.
    If the term does not contain any sets anyway and could not be simplified, returns NoTermConversionNeeded. *)
let rec get_rid_of_sets_in_trm (type_env:mapVarType) (type_info:typeInformation) (trm:form) : termConversionResult =
  match trm with
      Var v ->
	(try
	   let ty = MapOfVars.find v type_env in
	   (match try_get_rid_of_sets_in_type ty with
	       TypeExactlyConverted new_ty ->
		 TermExactlyConverted((MapOfVars.singleton v new_ty),type_info,trm)
	     | NonObjSetTypesPresent new_ty ->
	         TermNonObjSetsProbablyLeft((MapOfVars.singleton v new_ty),type_info,trm)
	     | NoTypeConversionNeeded -> NoTermConversionNeeded)
	 with Not_found -> NoTermConversionNeeded)
    | TypedForm(((Var v) as var),ty) ->
        (match try_get_rid_of_sets_in_type ty with
	    TypeExactlyConverted new_ty ->
	      let new_trm = FormUtil.mk_typedform (var,new_ty) in
	      let new_type_env = MapOfVars.singleton v new_ty in
	      TermExactlyConverted(new_type_env,type_info,new_trm)
	  | NonObjSetTypesPresent new_ty ->
	      let new_trm = FormUtil.mk_typedform (var,new_ty) in
	      let new_type_env = MapOfVars.singleton v new_ty in
	      TermNonObjSetsProbablyLeft(new_type_env,type_info,new_trm)
	  | NoTypeConversionNeeded -> NoTermConversionNeeded)
    | Const Elem | App(Const Elem,[]) -> TermApproximationNeeded
    | TypedForm(Const Elem,ty) | TypedForm(App(Const Elem,[]),ty) | App(TypedForm(Const Elem,ty),[])->
        (match FormUtil.normalize_type ty with
	    TypeFun([ty1;TypeApp(TypeSet,[ty2])],TypeApp(TypeBool,[])) when ty1=ty2 ->
	      if FormUtil.is_object_type ty1 then
		match type_info.member_symb with
		    Some str -> 
		      let typed_var = FormUtil.mk_typedvar str member_obj_objset_type in
		      TermExactlyConverted(MapOfVars.empty,type_info,typed_var)
		  | None ->
		      let str = Util.fresh_name (member_prefix^(FormUtil.objset_str)) in
		      let typed_var = FormUtil.mk_typedvar str member_obj_objset_type in
		      let new_type_info = { type_info with member_symb = Some str } in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,typed_var)
	      else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
	  | _ -> failwith("get_rid_of_sets_in_trm: the membership relation should map an element of some type and a set of elements of the same type to a boolean, but it does not: "^(PrintForm.string_of_form trm)^".\n"))
    | Const Disjoint -> TermApproximationNeeded
    | TypedForm((Const Disjoint),ty) ->
        (match FormUtil.normalize_type ty with
	    TypeFun(lst,TypeApp(TypeBool,[])) ->
	      let no_of_args = List.length lst in
	      let new_ty = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) FormUtil.mk_bool_type in
              if List.for_all is_objset_type lst then
		try
		  let disj_str = MapOfInts.find no_of_args type_info.disjoint_symb in
		  let typed_disj_var = FormUtil.mk_typedvar disj_str new_ty in
		  TermExactlyConverted(MapOfVars.empty,type_info,typed_disj_var)
		with Not_found ->
		  let disj_str = Util.fresh_name (disjoint_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
		  let typed_disj_var = FormUtil.mk_typedvar disj_str new_ty in
		  let new_disjoint_symb = MapOfInts.add no_of_args disj_str type_info.disjoint_symb in
		  let new_type_info = { type_info with disjoint_symb = new_disjoint_symb } in
		  TermExactlyConverted(MapOfVars.empty,new_type_info,typed_disj_var)
	      else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
	  | TypeApp(TypeBool,[]) -> TermExactlyConverted(MapOfVars.empty,type_info,FormUtil.mk_true)
	  | _ ->  failwith ("get_rid_of_sets_in_trm: disjoint symbol should be typed as a map from a list of sets to booleans, but it is not: "^(PrintForm.string_of_form trm)^".\n"))
    | Const LtEq | App(Const LtEq, []) ->
        TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
    | Const Subseteq | App(Const Subseteq, [])->
        TermApproximationNeeded
    | TypedForm(Const Subseteq, TypeFun([ty1;ty2],TypeApp(TypeBool,[]))) | App(TypedForm(Const Subseteq, TypeFun([ty1;ty2],TypeApp(TypeBool,[]))),[]) | TypedForm(App(Const Subseteq,[]), TypeFun([ty1;ty2],TypeApp(TypeBool,[]))) ->
        if FormUtil.equal_types ty1 ty2 then
	  match FormUtil.normalize_type ty1 with
	      TypeApp(TypeSet,[ty]) ->
		if is_objset_type ty then
		  match type_info.subseteq_symb with
		      Some subseteq_str -> 
			let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			TermExactlyConverted(MapOfVars.empty,type_info,typed_subseteq_var)
		    | None ->
		        let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			let new_type_info = { type_info with subseteq_symb = Some subseteq_str } in
			TermExactlyConverted(MapOfVars.empty,new_type_info,typed_subseteq_var)
		else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
	    | _ ->
	        failwith ("get_rid_of_sets_in_trm: subset relations can be checked only between sets, but this subset symbol is ill-typed: "^(PrintForm.string_of_form trm)^".\n")
	else
          failwith ("get_rid_of_sets_in_trm: subset relations can be checked only between same-typed sets, but this subset symbol is ill-typed: "^(PrintForm.string_of_form trm)^".\n")
    | TypedForm(Const LtEq, TypeFun([ty1;ty2],TypeApp(TypeBool,[])))  | App(TypedForm(Const LtEq, TypeFun([ty1;ty2],TypeApp(TypeBool,[]))),[]) | TypedForm(App(Const LtEq,[]), TypeFun([ty1;ty2],TypeApp(TypeBool,[])))->
        if FormUtil.equal_types ty1 ty2 then
	  match FormUtil.normalize_type ty1 with
	      TypeApp(TypeSet,[ty]) ->
		if is_objset_type ty then
		  match type_info.subseteq_symb with
		      Some subseteq_str -> 
			let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			TermExactlyConverted(MapOfVars.empty,type_info,typed_subseteq_var)
		    | None ->
		        let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			let new_type_info = { type_info with subseteq_symb = Some subseteq_str } in
			TermExactlyConverted(MapOfVars.empty,new_type_info,typed_subseteq_var)
		else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
	    | _ -> NoTermConversionNeeded
	else
          failwith ("get_rid_of_sets_in_trm: less-than-or-equal-to relation can be checked only between same-typed sets, but this less-than-or-equal-to symbol is ill-typed: "^(PrintForm.string_of_form trm)^".\n")
    | Const Card | Const Cardeq | Const Cardleq | Const Cardgeq -> TermApproximationNeeded
    | TypedForm(Const Card,ty) ->
        (match FormUtil.normalize_type ty with
	    TypeFun([TypeApp(TypeSet,[ty1])],TypeApp(TypeInt,[])) ->
	      if FormUtil.is_object_type ty1 then
		match type_info.size_of_support_symb with
		    Some size_of_support_str ->	
		      let typed_var_size_of_support = FormUtil.mk_typedvar size_of_support_str size_of_support_of_objset_type in
		      TermExactlyConverted(MapOfVars.empty,type_info,typed_var_size_of_support)
		  | None ->
		      let size_of_support_str = Util.fresh_name (sizeOfSupport_prefix^(FormUtil.objset_str)) in
		      let typed_var_size_of_support = FormUtil.mk_typedvar size_of_support_str size_of_support_of_objset_type in
		      let new_type_info = { type_info with size_of_support_symb = Some size_of_support_str } in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,typed_var_size_of_support)
	      else 
		TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
	  | _ ->
              failwith ("get_rid_of_sets_in_trm: cardinality should map a set to a boolean, but it does not: "^(PrintForm.string_of_form trm)^".\n"))
    | TypedForm(Const Cardeq,ty) -> 
        (match FormUtil.normalize_type ty with
	    TypeFun([TypeApp(TypeSet,[ty1]);TypeApp(TypeInt,[])],TypeApp(TypeBool,[])) ->
	      if FormUtil.is_object_type ty1 then 
		match type_info.size_of_support_is_exactly_constant with
		    Some str ->	
		      let typed_var_sosiec = FormUtil.mk_typedvar str size_of_support_of_objset_is_constant_type in
		      TermExactlyConverted(MapOfVars.empty,type_info,typed_var_sosiec)
		  | None -> 
		      let str = Util.fresh_name (sizeOfSupportIsExactlyConstant_prefix^(FormUtil.objset_str)) in
		      let typed_var_sosiec = FormUtil.mk_typedvar str size_of_support_of_objset_is_constant_type in
		      let new_type_info = { type_info with size_of_support_is_exactly_constant = Some str} in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,typed_var_sosiec)
	      else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
	  | _ -> 
              failwith ("get_rid_of_sets_in_trm: cardinality-of-a-set-equals-to-a-constant should map a set and an integer to a boolean, but it does not: "^(PrintForm.string_of_form trm)^".\n"))
    | TypedForm(Const Cardleq,ty) ->
        (match FormUtil.normalize_type ty with
	    TypeFun([TypeApp(TypeSet,[ty1]);TypeApp(TypeInt,[])],TypeApp(TypeBool,[])) ->
	      if FormUtil.is_object_type ty1 then 
		match type_info.size_of_support_is_at_most_constant with
		    Some str ->	
		      let typed_var_sosiamc = FormUtil.mk_typedvar str size_of_support_of_objset_is_constant_type in
		      TermExactlyConverted(MapOfVars.empty,type_info,typed_var_sosiamc)
		  | None ->
		      let str = Util.fresh_name (sizeOfSupportIsAtMostConstant_prefix^(FormUtil.objset_str)) in
		      let typed_var_sosiamc = FormUtil.mk_typedvar str size_of_support_of_objset_is_constant_type in
		      let new_type_info = { type_info with size_of_support_is_at_most_constant = Some str } in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,typed_var_sosiamc)
	      else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
	  | _ -> 
              failwith ("get_rid_of_sets_in_trm: cardinality-of-a-set-is-at-most-a-constant should map a set and an integer to a boolean, but it does not: "^(PrintForm.string_of_form trm)^".\n"))
    | TypedForm(Const Cardgeq,ty) ->
        (match FormUtil.normalize_type ty with
	    TypeFun([TypeApp(TypeSet,[ty1]);TypeApp(TypeInt,[])],TypeApp(TypeBool,[])) ->
	      if FormUtil.is_object_type ty1 then 
		match type_info.size_of_support_is_at_least_constant with
		    Some str ->	
		      let typed_var_sosialc = FormUtil.mk_typedvar str size_of_support_of_objset_is_constant_type in
		      TermExactlyConverted(MapOfVars.empty,type_info,typed_var_sosialc)
		  | None -> 
		      let str = Util.fresh_name (sizeOfSupportIsAtLeastConstant_prefix^(FormUtil.objset_str)) in
		      let typed_var_sosialc = FormUtil.mk_typedvar str size_of_support_of_objset_is_constant_type in
		      let new_type_info = { type_info with size_of_support_is_at_least_constant = Some str} in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,typed_var_sosialc)
	      else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
	  | _ -> 
              failwith ("get_rid_of_sets_in_trm: cardinality-of-a-set-is-at-least-a-constant should map a set and an integer to a boolean, but it does not: "^(PrintForm.string_of_form trm)^".\n"))
    | Const Cap | Const Cup -> TermApproximationNeeded
    | TypedForm(Const Cap,ty) ->
        (match FormUtil.normalize_type ty with
	    TypeFun(type_list,type_res) -> 
	      if is_objset_type type_res then
		let no_of_args = List.length type_list in
		let inter_var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
		try
		  let inter_str = MapOfInts.find no_of_args type_info.intersection_symb in
		  let typed_inter_var = FormUtil.mk_typedvar inter_str inter_var_type in
		  TermExactlyConverted(MapOfVars.empty,type_info,typed_inter_var)
		with Not_found ->
		  let inter_str = Util.fresh_name (intersection_prefix^(string_of_int no_of_args)^(FormUtil.objset_str)) in
		  let typed_inter_var = FormUtil.mk_typedvar inter_str inter_var_type in
		  let new_intersection_symb = MapOfInts.add no_of_args inter_str type_info.intersection_symb in
		  let new_type_info = { type_info with intersection_symb = new_intersection_symb } in
		  TermExactlyConverted(MapOfVars.empty,new_type_info,typed_inter_var)		  
	      else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
	  | type_res ->
              if is_objset_type type_res then
                (match type_info.universalset_symb with
	      	    Some univ_set_str -> 
		      let typed_var_univ_set = FormUtil.mk_typedvar univ_set_str predicate_on_objects_type in
		      TermExactlyConverted(MapOfVars.empty,type_info,typed_var_univ_set)
		  | None ->
	              let univ_set_str = Util.fresh_name (universalSet_prefix^(FormUtil.objset_str)) in
		      let typed_var_univ_set = FormUtil.mk_typedvar univ_set_str predicate_on_objects_type in
		      let new_type_info = { type_info with universalset_symb = (Some univ_set_str) } in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,typed_var_univ_set))
	      else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm))
    | TypedForm(Const Cup,ty) ->
        (match FormUtil.normalize_type ty with
	    TypeFun(type_list,type_res) -> 
	      if is_objset_type type_res then
		let no_of_args = List.length type_list in
		let union_var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
		try 
		  let union_str = MapOfInts.find no_of_args type_info.union_symb in
		  let typed_union_var = FormUtil.mk_typedvar union_str union_var_type in
		  TermExactlyConverted(MapOfVars.empty,type_info,typed_union_var)
		with Not_found ->
		  let union_str = Util.fresh_name (union_prefix^(string_of_int no_of_args)^(FormUtil.objset_str)) in
		  let typed_union_var = FormUtil.mk_typedvar union_str union_var_type in
		  let new_union_symb = MapOfInts.add no_of_args union_str type_info.union_symb in
		  let new_type_info = { type_info with union_symb = new_union_symb } in
		  TermExactlyConverted(MapOfVars.empty,new_type_info,typed_union_var)
	      else
		TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
	  | type_res ->
              if is_objset_type type_res then
		(match type_info.emptyset_symb with
		    Some emptyset_str ->
		      let typed_var_emptyset = FormUtil.mk_typedvar emptyset_str predicate_on_objects_type in
		      TermExactlyConverted(MapOfVars.empty,type_info,typed_var_emptyset)
		  | None ->
                      let emptyset_str = Util.fresh_name (emptySet_prefix^(FormUtil.objset_str)) in
		      let typed_var_emptyset = FormUtil.mk_typedvar emptyset_str predicate_on_objects_type in
		      let new_type_info = { type_info with emptyset_symb = Some emptyset_str } in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,typed_var_emptyset))
	      else
		TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm))
    | Const Minus | App(Const Minus,[]) -> 
        TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
    | TypedForm(Const Minus,ty) | TypedForm(App((Const Minus),[]),ty) | App(TypedForm(Const Minus,ty),[]) ->
        (match FormUtil.normalize_type ty with
	    TypeFun([ty1;ty2],ty3) when ((FormUtil.equal_types ty1 ty2) && (FormUtil.equal_types ty2 ty3)) ->
	      (match ty1 with
		  TypeApp(TypeSet,[ty4]) ->
		    if FormUtil.is_object_type ty4 then 
		      match type_info.difference_symb with
			  Some diff_str ->
			    let typed_diff_var = FormUtil.mk_typedvar diff_str operator_on_object_predicates_type in
			    TermExactlyConverted(MapOfVars.empty,type_info,typed_diff_var)
			| None ->
			    let diff_str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			    let typed_diff_var = FormUtil.mk_typedvar diff_str operator_on_object_predicates_type in
			    let new_type_info = { type_info with difference_symb = Some diff_str } in
			    TermExactlyConverted(MapOfVars.empty,new_type_info,typed_diff_var)
		    else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
		| _ ->
		    NoTermConversionNeeded)
	  | _ ->
              failwith ("get_rid_of_sets_in_trm: subtraction should be typed as a map from two arguments of the same type to an argument of the same type as the first two, but it is not: "^(PrintForm.string_of_form trm)^".\n"))
    | Const Diff | App((Const Diff),[]) -> TermApproximationNeeded
    | TypedForm((Const Diff),ty) | TypedForm(App((Const Diff),[]),ty) | App(TypedForm((Const Diff),ty),[])->
        (match FormUtil.normalize_type ty with
	    TypeFun([ty1;ty2],ty3) when ((FormUtil.equal_types ty1 ty2) && (FormUtil.equal_types ty2 ty3)) ->
	      (match ty1 with
		  TypeApp(TypeSet,[ty4]) ->
		    if FormUtil.is_object_type ty4 then 
		      match type_info.difference_symb with
			  Some diff_str ->
			    let typed_diff_var = FormUtil.mk_typedvar diff_str operator_on_object_predicates_type in
			    TermExactlyConverted(MapOfVars.empty,type_info,typed_diff_var)
			| None ->
			    let diff_str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			    let typed_diff_var = FormUtil.mk_typedvar diff_str operator_on_object_predicates_type in
			    let new_type_info = { type_info with difference_symb = Some diff_str } in
			    TermExactlyConverted(MapOfVars.empty,new_type_info,typed_diff_var)
		    else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
		| _ ->
		  failwith ("get_rid_of_sets_in_trm: set difference should be typed as an operator on sets, but it is not: "^(PrintForm.string_of_form trm)^".\n"))
	  | _ -> 
             failwith ("get_rid_of_sets_in_trm: set difference should be typed as a map from two arguments of the same type to an argument of the same type as the first two, but it is not: "^(PrintForm.string_of_form trm)^".\n"))
    | Const Subset | App((Const Subset), []) -> TermApproximationNeeded
    | TypedForm(Const Subset,ty) | TypedForm(App(Const Subset,[]),ty) | App(TypedForm(Const Subset,ty),[])  ->
        (match FormUtil.normalize_type ty with
	    TypeFun([TypeApp(TypeSet,[ty1]);TypeApp(TypeSet,[ty2])],TypeApp(TypeBool,[])) when FormUtil.equal_types ty1 ty2 ->
	      if FormUtil.is_object_type ty1 then
		  match type_info.strictSubset_symb with
		      Some strictSubset_str -> 
			let typed_strictSubset_var = FormUtil.mk_typedvar strictSubset_str test_on_two_object_predicates_type in
			TermExactlyConverted(MapOfVars.empty,type_info,typed_strictSubset_var)
		    | None ->
		      let strictSubset_str = Util.fresh_name (strictSubset_prefix^(FormUtil.objset_str)) in
		      let typed_strictSubset_var = FormUtil.mk_typedvar strictSubset_str test_on_two_object_predicates_type in
		      let new_type_info = { type_info with strictSubset_symb = Some strictSubset_str } in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,typed_strictSubset_var)
	      else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
	  | _ ->  failwith ("get_rid_of_sets_in_trm: subset relation should take two set arguments over the same type and return a boolean, but it does not: "^(PrintForm.string_of_form trm)^".\n"))
    | Const Seteq | App(Const Seteq,[]) ->
        TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
    | TypedForm(Const Seteq,ty) | App(TypedForm(Const Seteq,ty),[]) | TypedForm(App(Const Seteq,[]),ty) ->
        (match FormUtil.normalize_type ty with
	    TypeFun([TypeApp(TypeSet,[ty1]);TypeApp(TypeSet,[ty2])],TypeApp(TypeBool,[])) when FormUtil.equal_types ty1 ty2 ->
	      if FormUtil.is_object_type ty1 then
		let typed_const = FormUtil.mk_typedform(Const Eq,test_on_two_object_predicates_type) in
		TermExactlyConverted(MapOfVars.empty,type_info,typed_const)
	      else TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
	  | _ ->  failwith ("get_rid_of_sets_in_trm: the set equality relation should take two set arguments over the same type and return a boolean, but it does not: "^(PrintForm.string_of_form trm)^".\n"))
    | Const Eq | App(Const Eq,[]) | Const MetaEq | App(Const MetaEq,[]) ->
        TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm)
    | TypedForm(((Const Eq) as c),ty) | TypedForm(App(((Const Eq) as c),[]),ty) | App(TypedForm(((Const Eq) as c),ty),[])
    | TypedForm(((Const MetaEq) as c),ty) | TypedForm(App(((Const MetaEq) as c),[]),ty) | App(TypedForm(((Const MetaEq) as c),ty),[]) ->
        (match try_get_rid_of_sets_in_type ty with
	    TypeExactlyConverted new_ty ->
	      let new_trm = FormUtil.mk_typedform(c,new_ty) in
	      TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
	  | NonObjSetTypesPresent new_ty ->
	      let new_trm = FormUtil.mk_typedform(c,new_ty) in
	      TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,new_trm)
	  | NoTypeConversionNeeded -> NoTermConversionNeeded)
    | Const EmptysetConst | App(Const EmptysetConst,[]) | App(Const FiniteSetConst,[]) -> TermApproximationNeeded
    | TypedForm((Const EmptysetConst),ty) | TypedForm(App(Const EmptysetConst,[]),ty) | App(TypedForm(Const EmptysetConst,ty),[]) 
    | TypedForm(App(Const FiniteSetConst,[]),ty) ->
        (match FormUtil.normalize_type ty with
	    TypeApp(TypeSet,[ty1]) ->
	      if FormUtil.is_object_type ty1 then
		match type_info.emptyset_symb with
		    Some str -> 
		      let typed_var = FormUtil.mk_typedvar str predicate_on_objects_type in
		      TermExactlyConverted(MapOfVars.empty,type_info,typed_var)
		  | None ->
		      let str = Util.fresh_name (emptySet_prefix^(FormUtil.objset_str)) in
		      let typed_var = FormUtil.mk_typedvar str predicate_on_objects_type in
		      let new_type_info = { type_info with emptyset_symb = Some str } in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,typed_var)
	      else TermApproximationNeeded
	  | _ -> failwith ("get_rid_of_sets_in_trm: the empty set should have a set type, but it does not in the following input: "^(PrintForm.string_of_form trm)^".\n"))
    | Const FiniteSetConst ->
        TermApproximationNeeded
    | TypedForm(Const FiniteSetConst,ty) ->
        (match FormUtil.normalize_type ty with
	    TypeFun(type_list,type_res) ->
	      (match type_res with
		  TypeApp(TypeSet,[ty1]) ->
		    let no_of_args = List.length type_list in
		    if FormUtil.is_object_type ty1 then
		      if no_of_args = 1 then
			let var_ty = FormUtil.mk_fun_type [ty1;ty1] FormUtil.mk_bool_type in
			let typed_const = FormUtil.mk_typedform(Const Eq,var_ty) in
			TermExactlyConverted(MapOfVars.empty,type_info,typed_const)
		      else
			let var_ty = FormUtil.mk_fun_type (make_list_of_identical_items FormUtil.mk_object_type no_of_args) predicate_on_objects_type in
			try 
			  let str = MapOfInts.find no_of_args type_info.finiteSet_symb in
			  let typed_var = FormUtil.mk_typedvar str var_ty in
			  TermExactlyConverted(MapOfVars.empty,type_info,typed_var)
			with Not_found ->
			  let str = Util.fresh_name (finiteSet_prefix^(FormUtil.objset_str)) in
			  let new_finiteSet_symb = MapOfInts.add no_of_args str type_info.finiteSet_symb in
			  let new_type_info = { type_info with finiteSet_symb = new_finiteSet_symb } in
			  let typed_var = FormUtil.mk_typedvar str var_ty in
			  TermExactlyConverted(MapOfVars.empty,new_type_info,typed_var)
		    else TermApproximationNeeded
		| _ -> failwith ("get_rid_of_sets_in_trm: the finite set constructor should return a set, but it does not: "^(PrintForm.string_of_form trm)^".\n"))
	  | type_res ->
	      if is_objset_type type_res then
		match type_info.emptyset_symb with
		    Some str -> 
		      let typed_var = FormUtil.mk_typedvar str predicate_on_objects_type in
		      TermExactlyConverted(MapOfVars.empty,type_info,typed_var)
		  | None ->
		      let str = Util.fresh_name (emptySet_prefix^(FormUtil.objset_str)) in
		      let typed_var = FormUtil.mk_typedvar str predicate_on_objects_type in
		      let new_type_info = {type_info with emptyset_symb=Some str} in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,typed_var)
	      else
		TermApproximationNeeded)
    | Const UniversalSetConst | App(Const UniversalSetConst, []) ->
        TermApproximationNeeded
    | TypedForm(Const UniversalSetConst,ty) | TypedForm(App(Const UniversalSetConst,[]),ty) | App(TypedForm(Const UniversalSetConst,ty),[])  ->
        (match FormUtil.normalize_type ty with
	    TypeApp(TypeSet,[ty1]) ->
	      if FormUtil.is_object_type ty1 then
		match type_info.universalset_symb with
		    Some str ->
		      let typed_var = FormUtil.mk_typedvar str predicate_on_objects_type in
		      TermExactlyConverted(MapOfVars.empty,type_info,typed_var)
		  | None ->
		      let str = Util.fresh_name (universalSet_prefix^(FormUtil.objset_str)) in
		      let typed_var = FormUtil.mk_typedvar str predicate_on_objects_type in
		      let new_type_info = {type_info with universalset_symb=Some str} in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,typed_var)
	      else TermApproximationNeeded
	  | _ -> failwith ("get_rid_of_sets_in_trm: the universal set should have a set type, but it does not: "^(PrintForm.string_of_form trm)^".\n"))
    | Const Rtrancl | TypedForm(Const Rtrancl,_) | Const Rimage | TypedForm(Const Rimage,_) | Const ObjLocs | TypedForm(Const ObjLocs, _)
        -> TermApproximationNeeded
    | Const _ -> NoTermConversionNeeded
    | TypedForm(((Const _) as c) ,ty) ->
        (match try_get_rid_of_sets_in_type ty with
	    TypeExactlyConverted new_ty -> TermExactlyConverted(MapOfVars.empty,type_info,(TypedForm(c,new_ty)))
	  | NonObjSetTypesPresent new_ty -> TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,(TypedForm(c,new_ty)))
	  | NoTypeConversionNeeded -> NoTermConversionNeeded)
    | App((TypedForm((Var _),_) as op), args) | App((Var _) as op, args) ->
        (match get_rid_of_sets_in_trm type_env type_info op with
	    TermExactlyConverted(updated_vars_after_op,updated_type_info,new_op) ->
	      (match get_rid_of_sets_in_trm_list type_env updated_type_info args with
		  TermListExactlyConverted(more_vars,new_type_info,new_args) ->
		    TermExactlyConverted((unionMapVarType_preferFirst more_vars updated_vars_after_op),new_type_info,(App(new_op,new_args)))
		| TermListNonObjSetsProbablyLeft(more_vars,new_type_info,new_args) ->
		    TermNonObjSetsProbablyLeft((unionMapVarType_preferFirst more_vars updated_vars_after_op),new_type_info,(App(new_op,new_args)))
		| TermListApproximationNeeded -> TermApproximationNeeded
		| NoTermListConversionNeeded -> TermExactlyConverted(updated_vars_after_op,updated_type_info,(App(new_op,args))))
	  | TermNonObjSetsProbablyLeft(updated_vars_after_op,updated_type_info,new_op) ->
	      (match get_rid_of_sets_in_trm_list type_env updated_type_info args with
		  TermListExactlyConverted(more_vars,new_type_info,new_args)
		| TermListNonObjSetsProbablyLeft(more_vars,new_type_info,new_args) ->
		    TermNonObjSetsProbablyLeft((unionMapVarType_preferFirst more_vars updated_vars_after_op),new_type_info,(App(new_op,new_args)))
		| TermListApproximationNeeded -> TermApproximationNeeded
		| NoTermListConversionNeeded -> TermNonObjSetsProbablyLeft(updated_vars_after_op,updated_type_info,(App(new_op,args))))
	  | TermApproximationNeeded -> TermApproximationNeeded
	  | NoTermConversionNeeded -> 
	      (match get_rid_of_sets_in_trm_list type_env type_info args with
		  TermListExactlyConverted(more_vars,new_type_info,new_args) ->
		    TermExactlyConverted(more_vars,new_type_info,(App(op,new_args)))
		| TermListNonObjSetsProbablyLeft(more_vars,new_type_info,new_args) ->
		    TermNonObjSetsProbablyLeft(more_vars,new_type_info,(App(op,new_args)))
		| TermListApproximationNeeded -> TermApproximationNeeded
		| NoTermListConversionNeeded -> NoTermConversionNeeded))
    | App(Const Seteq,([TypedForm(arg1,set_ty1);TypedForm(arg2,set_ty2)] as args)) ->
        if FormUtil.equal_types set_ty1 set_ty2 then 
	  (match set_ty1 with
	      TypeApp(TypeSet,[TypeApp(TypeObject,[])]) ->
		(match get_rid_of_sets_in_trm_list type_env type_info args with
		    TermListExactlyConverted(new_vars,updated_type_info,[converted_arg1;converted_arg2]) ->
		      let new_arg1 = overwritingly_attach_type converted_arg1 predicate_on_objects_type in
		      let new_arg2 = overwritingly_attach_type converted_arg2 predicate_on_objects_type in
		      let new_trm = App(Const Eq,[new_arg1;new_arg2]) in
		      TermExactlyConverted(new_vars,updated_type_info,new_trm)
		  | TermListNonObjSetsProbablyLeft(new_vars,updated_type_info,[converted_arg1;converted_arg2]) ->
		      let new_arg1 = overwritingly_attach_type converted_arg1 predicate_on_objects_type in
		      let new_arg2 = overwritingly_attach_type converted_arg2 predicate_on_objects_type in
		      let new_trm = App(Const Eq,[new_arg1;new_arg2]) in
		      TermNonObjSetsProbablyLeft(new_vars,updated_type_info,new_trm)
		  | TermListApproximationNeeded -> TermApproximationNeeded
		  | NoTermListConversionNeeded -> 
		      let _ = Util.warn ("get_rid_of_sets_in_trm: arguments of Seteq have set-of-object type, they should have been rewritten to predicates, but they have not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		      let new_arg1 = overwritingly_attach_type arg1 predicate_on_objects_type in
		      let new_arg2 = overwritingly_attach_type arg2 predicate_on_objects_type in
		      let new_trm = App(Const Eq,[new_arg1;new_arg2]) in
		      TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
		  | _ -> failwith ("get_rid_of_sets_in_trm: conversion of a list of two elements should return a list of two elements, but it did not in the following input: "^(PrintForm.string_of_form trm)^".\n"))
	    | TypeApp(TypeSet,_) -> TermApproximationNeeded
	    | _ -> failwith ("get_rid_of_sets_in_trm: the set-equality should accepts sets as arguments, but it does not: "^(PrintForm.string_of_form trm)^".\n"))
	else failwith ("get_rid_of_sets_in_trm: the set-equality should map two same-type sets to a boolean, but it does not: "^(PrintForm.string_of_form trm)^".\n")
    | App(Const Seteq,[TypedForm(_,set_ty) as typed_arg]) ->
        (match FormUtil.normalize_type set_ty with
	    TypeApp(TypeSet,[ty]) ->
	      if FormUtil.is_object_type ty then
		(match get_rid_of_sets_in_trm type_env type_info typed_arg with
		    TermExactlyConverted(new_vars,updated_type_info,converted_arg) ->
		      let new_arg = overwritingly_attach_type converted_arg predicate_on_objects_type in
		      let new_trm = App(Const Eq,[new_arg]) in
		      TermExactlyConverted(new_vars,updated_type_info,new_trm)
		  | TermNonObjSetsProbablyLeft(new_vars,updated_type_info,converted_arg) ->
  		      let new_arg = overwritingly_attach_type converted_arg predicate_on_objects_type in
		      let new_trm = App(Const Eq,[new_arg]) in
		      TermNonObjSetsProbablyLeft(new_vars,updated_type_info,new_trm)
		  | TermApproximationNeeded -> TermApproximationNeeded
		  | NoTermConversionNeeded ->
		      let _ = Util.warn ("get_rid_of_sets_in_trm: the argument of SetEq has the set-of-object type, it should be rewritten to predicates, but it was not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		      let new_arg = overwritingly_attach_type typed_arg predicate_on_objects_type in
		      let new_trm = App(Const Eq,[new_arg]) in
		      TermExactlyConverted(MapOfVars.empty,type_info,new_trm))
	      else TermApproximationNeeded
	  | _ -> failwith ("get_rid_of_sets_in_trm: the argument(s) of set-equality should be sets, but they are not: "^(PrintForm.string_of_form trm)^".\n"))
    | App(Const Seteq,args) ->
        (match get_rid_of_sets_in_trm_list type_env type_info args with
	    TermListExactlyConverted(new_vars,updated_type_info,converted_args) ->
	      let new_trm = App(Const Eq,converted_args) in
	      TermExactlyConverted(new_vars,updated_type_info,new_trm)
	  | TermListNonObjSetsProbablyLeft(new_vars,updated_type_info,converted_args) ->
	      let te = mapVarType2typeEnv type_env in
	      if List.for_all (fun f -> FormUtil.is_object_type (TypeReconstruct.get_type te f)) converted_args then
		let new_trm = App(Const Eq,converted_args) in
		TermNonObjSetsProbablyLeft(new_vars,updated_type_info,new_trm)
	      else TermApproximationNeeded
	  | TermListApproximationNeeded -> TermApproximationNeeded
	  | NoTermListConversionNeeded -> 
	      let _ = Util.warn ("get_rid_of_sets_in_trm: the argument of Seteq has a set type, it cannot be left as it is, but it was in the following input: "^(PrintForm.string_of_form trm)^".\n") in
	      let new_trm = App(Const Eq,args) in
	      TermExactlyConverted(MapOfVars.empty,type_info,new_trm))
    | App(Const Elem,([TypedForm(elem,elem_ty);TypedForm(set_expr,set_ty)] as args)) ->
        (match set_ty with
	    TypeApp(TypeSet,[ty]) -> 
	      if FormUtil.equal_types ty elem_ty then
		if FormUtil.is_object_type ty then
		  (match get_rid_of_sets_in_trm_list type_env type_info args with
		      TermListExactlyConverted(new_types,updated_type_info,[converted_elem;converted_set_expr]) ->
			let new_elem = overwritingly_attach_type converted_elem (FormUtil.mk_object_type) in
			let new_pred = overwritingly_attach_type converted_set_expr predicate_on_objects_type in
			let new_trm = App(new_pred,[new_elem]) in
			TermExactlyConverted(new_types,updated_type_info,new_trm)
		    | TermListNonObjSetsProbablyLeft(new_types,updated_type_info,[converted_elem;converted_set_expr]) ->
			let new_elem = overwritingly_attach_type converted_elem (FormUtil.mk_object_type) in
			let new_pred = overwritingly_attach_type converted_set_expr predicate_on_objects_type in
			let new_trm = App(new_pred,[new_elem]) in
			TermNonObjSetsProbablyLeft(new_types,updated_type_info,new_trm)
		    | TermListApproximationNeeded -> TermApproximationNeeded
		    | NoTermListConversionNeeded ->
		        let _ = Util.warn ("get_rid_of_sets_in_trm: the set expression has not been converted although it should have been in the following formula "^(PrintForm.string_of_form trm)^".\n") in
			let new_elem = overwritingly_attach_type elem (FormUtil.mk_object_type) in
			let new_pred = overwritingly_attach_type set_expr predicate_on_objects_type in
			let new_trm = App(new_pred,[new_elem]) in
			TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
		    | _ -> failwith ("get_rid_of_sets_in_trm: conversion of a list of two elements should return a list of two elements, but it did not in the following input: "^(PrintForm.string_of_form trm)^".\n"))
		else TermApproximationNeeded
	      else failwith ("get_rid_of_sets_in_trm: the membership of an element of one type is checked against a set of elements of another type in the following input: "^(PrintForm.string_of_form trm)^".\n")
	  | _ -> failwith ("get_rid_of_sets_in_trm: the membership is checked against a non-set in the following input: "^(PrintForm.string_of_form trm)^".\n"))
    | App(Const Elem,([TypedForm(elem,elem_ty);set_expr] as args)) ->
        if FormUtil.is_object_type elem_ty then
	  (match get_rid_of_sets_in_trm_list type_env type_info args with
	      TermListExactlyConverted(new_types,updated_type_info,[converted_elem;converted_set_expr]) ->
		let new_elem = overwritingly_attach_type converted_elem FormUtil.mk_object_type in
		let new_trm = App(converted_set_expr,[new_elem]) in
		TermExactlyConverted(new_types,updated_type_info,new_trm)
	    | TermListNonObjSetsProbablyLeft(new_types,updated_type_info,[converted_elem;converted_set_expr]) ->
		let new_elem = overwritingly_attach_type converted_elem FormUtil.mk_object_type in
		let new_trm = App(converted_set_expr,[new_elem]) in
		TermNonObjSetsProbablyLeft(new_types,updated_type_info,new_trm)
	    | TermListApproximationNeeded -> TermApproximationNeeded
	    | NoTermListConversionNeeded -> 
	        let _ = Util.warn ("get_rid_of_sets_in_trm: an argument of the membership relation should have a set-of-object type, so it should be rewritten to a predicate, but it was not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
	        let new_elem = overwritingly_attach_type elem (FormUtil.mk_object_type) in
		let new_trm = App(set_expr,[new_elem]) in
		TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
	    | _ -> failwith ("get_rid_of_sets_in_trm: conversion of a list of two elements should return a list of two elements, but it did not in the following input: "^(PrintForm.string_of_form trm)^".\n"))
	else TermApproximationNeeded
    | App(Const Elem,([elem;TypedForm(set_expr,set_expr_ty)] as args)) ->
        (match FormUtil.normalize_type set_expr_ty with
	    TypeApp(TypeSet,[ty]) ->
	      if FormUtil.is_object_type ty then
		(match get_rid_of_sets_in_trm_list type_env type_info args with
		    TermListExactlyConverted(new_types,updated_type_info,[converted_elem;converted_set_expr]) ->
		      let new_pred = overwritingly_attach_type converted_set_expr predicate_on_objects_type in
		      let new_trm = App(new_pred,[converted_elem]) in
		      TermExactlyConverted(new_types,updated_type_info,new_trm)
		  | TermListNonObjSetsProbablyLeft(new_types,updated_type_info,[converted_elem;converted_set_expr]) ->
		      let new_pred = overwritingly_attach_type converted_set_expr predicate_on_objects_type in
		      let new_trm = App(new_pred,[converted_elem]) in
		      TermNonObjSetsProbablyLeft(new_types,updated_type_info,new_trm)
		  | TermListApproximationNeeded -> TermApproximationNeeded
		  | NoTermListConversionNeeded ->
	              let _ = Util.warn ("get_rid_of_sets_in_trm: an argument of the membership relation has the set-of-object type, it should be rewritten to a predicate, but it was not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
	              let new_set_expr = overwritingly_attach_type set_expr predicate_on_objects_type in
		      let new_trm = App(new_set_expr,[elem]) in
		      TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
		  | _ -> failwith ("get_rid_of_sets_in_trm: conversion of a list of two elements should return a list of two elements, but it did not in the following input: "^(PrintForm.string_of_form trm)^".\n"))
	      else TermApproximationNeeded
	  | _ -> failwith ("get_rid_of_sets_in_trm: membership in a non-set is checked: "^(PrintForm.string_of_form trm)^".\n"))
    | App(Const Elem, ([elem;set_expr] as args)) ->
        (match get_rid_of_sets_in_trm_list type_env type_info args with
	    TermListExactlyConverted(new_types,updated_type_info,[converted_elem;converted_set_expr]) ->
	      let new_trm = App(converted_set_expr,[converted_elem]) in
	      TermExactlyConverted(new_types,updated_type_info,new_trm)
	  | TermListNonObjSetsProbablyLeft(new_types,updated_type_info,[converted_elem;converted_set_expr]) ->
	      let new_trm = App(converted_set_expr,[converted_elem]) in
	      TermNonObjSetsProbablyLeft(new_types,updated_type_info,new_trm)
	  | TermListApproximationNeeded -> TermApproximationNeeded
	  | NoTermListConversionNeeded ->
	      let _ = Util.warn ("get_rid_of_sets_in_trm: an argument of the membership relation is a set of objects, it should be rewritten to a predicate, but it was not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
	      let new_trm = App(set_expr,[elem]) in
	      TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
	  | _ -> failwith ("get_rid_of_sets_in_trm: conversion of a list of two elements should return a list of two elements, but it did not in the following input: "^(PrintForm.string_of_form trm)^".\n"))
    | App(Const Elem,[TypedForm(elem,ty) as arg]) ->
        if FormUtil.is_object_type ty then
          (match get_rid_of_sets_in_trm type_env type_info elem with
  	      TermExactlyConverted(new_types,updated_type_info,converted_elem) ->
		let new_elem = attach_type_if_not_attached converted_elem (FormUtil.mk_object_type) in
		(match updated_type_info.member_symb with
		    Some str -> 
		      let typed_member_var = FormUtil.mk_typedvar str member_obj_objset_type in
		      let new_trm = App(typed_member_var,[new_elem]) in
		      TermExactlyConverted(new_types,updated_type_info,new_trm)
		  | None -> 
		      let str = Util.fresh_name (member_prefix^(FormUtil.objset_str)) in
		      let typed_member_var = FormUtil.mk_typedvar str member_obj_objset_type in
		      let new_trm = App(typed_member_var,[new_elem]) in
		      let new_type_info = { updated_type_info with member_symb = Some str } in
		      TermExactlyConverted(new_types,new_type_info,new_trm))
	    | TermNonObjSetsProbablyLeft(new_types,updated_type_info,converted_elem) ->
	        let new_elem = overwritingly_attach_type converted_elem (FormUtil.mk_object_type) in
		(match updated_type_info.member_symb with
		    Some str -> 
		      let typed_member_var = FormUtil.mk_typedvar str member_obj_objset_type in
		      let new_trm = App(typed_member_var,[new_elem]) in
		      TermNonObjSetsProbablyLeft(new_types,updated_type_info,new_trm)
		  | None -> 
		      let str = Util.fresh_name (member_prefix^(FormUtil.objset_str)) in
		      let typed_member_var = FormUtil.mk_typedvar str member_obj_objset_type in
		      let new_trm = App(typed_member_var,[new_elem]) in
		      let new_type_info = { updated_type_info with member_symb = Some str } in
		      TermNonObjSetsProbablyLeft(new_types,new_type_info,new_trm))
	    | TermApproximationNeeded -> TermApproximationNeeded
	    | NoTermConversionNeeded -> 
	        (match type_info.member_symb with
		    Some str -> 
		      let typed_member_var = FormUtil.mk_typedvar str member_obj_objset_type in
		      let new_trm = App(typed_member_var,[arg]) in
		      TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
		  | None -> 
		      let str = Util.fresh_name (member_prefix^(FormUtil.objset_str)) in
		      let typed_member_var = FormUtil.mk_typedvar str member_obj_objset_type in
		      let new_trm = App(typed_member_var,[arg]) in
		      let new_type_info = { type_info with member_symb = Some str } in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
	else TermApproximationNeeded
    | App(Const Elem,[elem]) ->
	(match TypeReconstruct.get_type (mapVarType2typeEnv type_env) elem with
	    TypeApp(TypeObject,[]) ->
              (match get_rid_of_sets_in_trm type_env type_info elem with
		  TermExactlyConverted(new_var_types,updated_type_info,converted_elem) ->
		    (match updated_type_info.member_symb with
			Some str ->
			  let typed_member_var = FormUtil.mk_typedvar str member_obj_objset_type in
			  let new_trm = App(typed_member_var,[converted_elem]) in
			  TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		      | None ->
			  let str = Util.fresh_name (member_prefix^(FormUtil.objset_str)) in
			  let typed_member_var = FormUtil.mk_typedvar str member_obj_objset_type in
			  let new_trm = App(typed_member_var,[converted_elem]) in
			  let new_type_info = { updated_type_info with member_symb = Some str } in
			  TermExactlyConverted(new_var_types,new_type_info,new_trm))
		| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_elem) ->
		    (match updated_type_info.member_symb with
			Some str ->
			  let typed_member_var = FormUtil.mk_typedvar str member_obj_objset_type in
			  let new_trm = App(typed_member_var,[converted_elem]) in
			  TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		      | None ->
			  let str = Util.fresh_name (member_prefix^(FormUtil.objset_str)) in
			  let typed_member_var = FormUtil.mk_typedvar str member_obj_objset_type in
			  let new_trm = App(typed_member_var,[converted_elem]) in
			  let new_type_info = { updated_type_info with member_symb = Some str } in
			  TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
		| TermApproximationNeeded -> TermApproximationNeeded
		| NoTermConversionNeeded -> 
                    (match type_info.member_symb with
			Some str ->
			  let typed_member_var = FormUtil.mk_typedvar str member_obj_objset_type in
			  let new_trm = App(typed_member_var,[elem]) in
			  TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
		      | None -> 
			  let str = Util.fresh_name (member_prefix^(FormUtil.objset_str)) in
			  let typed_member_var = FormUtil.mk_typedvar str member_obj_objset_type in
			  let new_trm = App(typed_member_var,[elem]) in
			  let new_type_info = { type_info with member_symb = Some str } in
			  TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
	  | _ -> TermApproximationNeeded)
    | App(((Const Eq) as c),args) | App(((Const MetaEq) as c),args) | App(((Const Or) as c),args) | App(((Const And) as c),args) | App(((Const MetaAnd) as c),args) | App(((Const Not) as c),args) | App(((Const Impl) as c),args) | App(((Const MetaImpl) as c),args) | App(((Const Iff) as c),args) | App(((Const Lt) as c),args) | App(((Const Gt) as c),args) | App(((Const GtEq) as c),args) | App(((Const ArrayRead) as c),args) | App(((Const ArrayWrite) as c),args) | App(((Const FieldRead) as c),args) | App(((Const FieldWrite) as c),args) | App(((Const UMinus) as c),args) | App(((Const Plus) as c),args) | App(((Const Mult) as c),args) | App(((Const Div) as c),args) | App(((Const Mod) as c),args) | App(((Const (IntConst _)) as c),args) | App(((Const (BoolConst _)) as c),args) | App(((Const NullConst) as c),args) | App(((Const (StringConst _)) as c),args) | App(((Const Tuple) as c),args) | App(((Const ListLiteral) as c),args) | App(((Const Let) as c),args) | App(((Const Unit) as c),args) | App(((Const Comment) as c),args) | App(((Const Old) as c),args) | App(((Const ObjLocs) as c),args) | App(((Const Ite) as c),args) ->
        (match get_rid_of_sets_in_trm_list type_env type_info args with
	    TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
	      let new_trm = App(c,converted_args) in
	      TermExactlyConverted(new_var_types,updated_type_info,new_trm)
	  | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
	      let new_trm = App(c,converted_args) in
	      TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
	  | TermListApproximationNeeded -> TermApproximationNeeded
	  | NoTermListConversionNeeded -> NoTermConversionNeeded)
    | App(Const Disjoint,args) ->
        let no_of_args = List.length args in
        if no_of_args <=1 then
	  TermExactlyConverted(MapOfVars.empty,type_info,(Const (BoolConst true)))
	else
	  let all_types = mapVarType2typeEnv type_env in
	  let get_ty = TypeReconstruct.get_type all_types in
	  if List.for_all (fun arg -> is_objset_type (get_ty arg)) args then
	    (match get_rid_of_sets_in_trm_list type_env type_info args with
		TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		  let new_ty = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) FormUtil.mk_bool_type in
	       	  (try
		     let disj_str = MapOfInts.find no_of_args updated_type_info.disjoint_symb in
		     let typed_disj_var = FormUtil.mk_typedvar disj_str new_ty in
		     let new_trm = App(typed_disj_var,converted_args) in
		     TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		   with Not_found ->
		     let disj_str = Util.fresh_name (disjoint_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
		     let typed_disj_var = FormUtil.mk_typedvar disj_str new_ty in
		     let new_disjoint_symb = MapOfInts.add no_of_args disj_str updated_type_info.disjoint_symb in
		     let new_type_info = { updated_type_info with disjoint_symb = new_disjoint_symb } in
		     let new_trm = App(typed_disj_var,converted_args) in
		     TermExactlyConverted(new_var_types,new_type_info,new_trm))
	      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		   let new_ty = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) FormUtil.mk_bool_type in
	       	   (try
		      let disj_str = MapOfInts.find no_of_args updated_type_info.disjoint_symb in
		      let typed_disj_var = FormUtil.mk_typedvar disj_str new_ty in
		      let new_trm = App(typed_disj_var,converted_args) in
		      TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		    with Not_found ->
		      let disj_str = Util.fresh_name (disjoint_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
		      let typed_disj_var = FormUtil.mk_typedvar disj_str new_ty in
		      let new_disjoint_symb = MapOfInts.add no_of_args disj_str updated_type_info.disjoint_symb in
		      let new_type_info = { updated_type_info with disjoint_symb = new_disjoint_symb } in
		      let new_trm = App(typed_disj_var,converted_args) in
		      TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
	      | TermListApproximationNeeded -> TermApproximationNeeded
	      | NoTermListConversionNeeded ->
	          let _ = Util.warn ("get_rid_of_sets_in_trm: disjoint operation took sets that should be converted to predicates, but they were not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		  let new_ty = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) FormUtil.mk_bool_type in
		  (try
		     let disj_str = MapOfInts.find no_of_args type_info.disjoint_symb in
		     let typed_disj_var = FormUtil.mk_typedvar disj_str new_ty in
		     let new_trm = App(typed_disj_var,args) in
		     TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
		   with Not_found ->
		     let disj_str = Util.fresh_name (disjoint_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
		     let typed_disj_var = FormUtil.mk_typedvar disj_str new_ty in
		     let new_disjoint_symb = MapOfInts.add no_of_args disj_str type_info.disjoint_symb in
		     let new_type_info = { type_info with disjoint_symb = new_disjoint_symb } in
		     let new_trm = App(typed_disj_var,args) in
		     TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
	  else TermApproximationNeeded
    | App(Const LtEq,([TypedForm(_,arg_ty1);TypedForm(_,arg_ty2)] as args)) ->
        if FormUtil.equal_types arg_ty1 arg_ty2 then
	  match FormUtil.normalize_type arg_ty1 with
	      TypeApp(TypeSet,[ty]) ->
		if FormUtil.is_object_type ty then
	        (match get_rid_of_sets_in_trm_list type_env type_info args with
		    TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		      let new_args = List.map (fun a -> overwritingly_attach_type a predicate_on_objects_type) converted_args in
		      (match updated_type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_type_info = { updated_type_info with subseteq_symb = Some subseteq_str } in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermExactlyConverted(new_var_types,new_type_info,new_trm))
		  | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		      let new_args = List.map (fun a -> overwritingly_attach_type a predicate_on_objects_type) converted_args in
		      (match updated_type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_type_info = { updated_type_info with subseteq_symb = Some subseteq_str } in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
		  | TermListApproximationNeeded -> TermApproximationNeeded
		  | NoTermListConversionNeeded ->
		      let _ = Util.warn ("get_rid_of_sets_in_trm: less-than-or-equal-to operation takes sets that should be converted to predicates, but they were not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		      let new_args = List.map (fun a -> overwritingly_attach_type a predicate_on_objects_type) args in
		      (match type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    let new_type_info = { type_info with subseteq_symb = Some subseteq_str } in
			    TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
		else TermApproximationNeeded
	    | _ -> 
	        (match get_rid_of_sets_in_trm_list type_env type_info args with
		    TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		      let new_trm = App(Const LtEq,converted_args) in
		      TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		  | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		      let new_trm = App(Const LtEq,converted_args) in
		      TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		  | TermListApproximationNeeded -> TermApproximationNeeded
		  | NoTermListConversionNeeded -> NoTermConversionNeeded)
	else failwith ("get_rid_of_sets_in_trm: the comparison should map two same-type elements to a boolean, but it does not: "^(PrintForm.string_of_form trm)^".\n")
    | App(Const LtEq,([TypedForm(a1,arg_ty1);a2] as args)) ->
        (match FormUtil.normalize_type arg_ty1 with
	    TypeApp(TypeSet,[ty]) -> 
	      if FormUtil.is_object_type ty then 
		(match get_rid_of_sets_in_trm_list type_env type_info args with
		    TermListExactlyConverted(new_var_types,updated_type_info,[converted_arg1;converted_arg2]) ->
		      let new_arg1 = overwritingly_attach_type converted_arg1 predicate_on_objects_type in
		      let new_args = [new_arg1;converted_arg2] in
		      (match updated_type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_type_info = { updated_type_info with subseteq_symb = Some subseteq_str } in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermExactlyConverted(new_var_types,new_type_info,new_trm))
		  | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,[converted_arg1;converted_arg2]) ->
		      let new_arg1 = overwritingly_attach_type converted_arg1 predicate_on_objects_type in
		      let new_args = [new_arg1;converted_arg2] in
		      (match updated_type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_type_info = { updated_type_info with subseteq_symb = Some subseteq_str } in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
		  | TermListApproximationNeeded -> TermApproximationNeeded
		  | NoTermListConversionNeeded ->
		      let _ = Util.warn ("get_rid_of_sets_in_trm: less-than-or-equal-to operation takes sets that should be converted to predicates, but they were not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		      let new_arg1 = overwritingly_attach_type a1 predicate_on_objects_type in
		      let new_args = [new_arg1;a2] in
		      (match type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    let new_type_info = { type_info with subseteq_symb = Some subseteq_str } in
			    TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
		  | _ -> failwith ("get_rid_of_sets_in_trm: conversion of a list of two elements should return a list of two elements, but it did not in the following input: "^(PrintForm.string_of_form trm)^".\n"))
	      else TermApproximationNeeded
	  | _ -> 
	    (match get_rid_of_sets_in_trm_list type_env type_info args with	    
		TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		  let new_trm = App(Const LtEq,converted_args) in
		  TermExactlyConverted(new_var_types,updated_type_info,new_trm)
	      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		  let new_trm = App(Const LtEq,converted_args) in
		  TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
	      | TermListApproximationNeeded -> TermApproximationNeeded
	      | NoTermListConversionNeeded -> NoTermConversionNeeded))
    | App(Const LtEq,([a1;TypedForm(a2,set_ty2)] as args)) ->
        (match set_ty2 with
	    TypeApp(TypeSet,[ty]) -> 
	      if FormUtil.is_object_type ty then 
		(match get_rid_of_sets_in_trm_list type_env type_info args with
		    TermListExactlyConverted(new_var_types,updated_type_info,[converted_arg1;converted_arg2]) ->
		      let new_arg2 = overwritingly_attach_type converted_arg2 predicate_on_objects_type in
		      let new_args = [converted_arg1;new_arg2] in
		      (match updated_type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_type_info = { updated_type_info with subseteq_symb = Some subseteq_str } in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermExactlyConverted(new_var_types,new_type_info,new_trm))
		  | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,[converted_arg1;converted_arg2]) ->
		      let new_arg2 = overwritingly_attach_type converted_arg2 predicate_on_objects_type in
		      let new_args = [converted_arg1;new_arg2] in
		      (match updated_type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_type_info = { updated_type_info with subseteq_symb = Some subseteq_str } in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
		  | TermListApproximationNeeded -> TermApproximationNeeded
		  | NoTermListConversionNeeded ->
		      let _ = Util.warn ("get_rid_of_sets_in_trm: less-than-or-equal-to operation takes sets that should be converted to predicates, but they were not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		      let new_arg2 = overwritingly_attach_type a2 predicate_on_objects_type in
		      let new_args = [a1;new_arg2] in
		      (match type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,new_args) in
			    let new_type_info = { type_info with subseteq_symb = Some subseteq_str } in
			    TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
		  | _ -> failwith ("get_rid_of_sets_in_trm: conversion of a list of two elements should return a list of two elements, but it did not in the following input: "^(PrintForm.string_of_form trm)^".\n"))
	      else TermApproximationNeeded
	  | _ -> 
	    (match get_rid_of_sets_in_trm_list type_env type_info args with	    
		TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		  let new_trm = App(Const LtEq,converted_args) in
		  TermExactlyConverted(new_var_types,updated_type_info,new_trm)
	      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		  let new_trm = App(Const LtEq,converted_args) in
		  TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
	      | TermListApproximationNeeded -> TermApproximationNeeded
	      | NoTermListConversionNeeded -> NoTermConversionNeeded))
    | App(Const LtEq,([a1;a2] as args)) ->
	let all_types = mapVarType2typeEnv type_env in
	let get_ty = TypeReconstruct.get_type all_types in
	let ty1 = get_ty a1 in
	let ty2 = get_ty a2 in
	if FormUtil.equal_types ty1 ty2 then
	  (match FormUtil.normalize_type ty1 with
	      TypeApp(TypeSet,[ty]) ->
		if FormUtil.is_object_type ty then
		  (match get_rid_of_sets_in_trm_list type_env type_info args with
		      TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
			(match updated_type_info.subseteq_symb with
			    Some subseteq_str ->
			      let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			      let new_trm = App(typed_subseteq_var,converted_args) in
			      TermExactlyConverted(new_var_types,updated_type_info,new_trm)
			  | None ->
  			      let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			      let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			      let new_type_info = { updated_type_info with subseteq_symb = Some subseteq_str } in
			      let new_trm = App(typed_subseteq_var,converted_args) in
			      TermExactlyConverted(new_var_types,new_type_info,new_trm))
		    | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
	                (match updated_type_info.subseteq_symb with
			    Some subseteq_str ->
			      let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			      let new_trm = App(typed_subseteq_var,converted_args) in
			      TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
			  | None ->
  			      let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			      let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			      let new_type_info = { updated_type_info with subseteq_symb = Some subseteq_str } in
			      let new_trm = App(typed_subseteq_var,converted_args) in
			      TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
		    | TermListApproximationNeeded -> TermApproximationNeeded
		    | NoTermListConversionNeeded ->
	                let _ = Util.warn ("get_rid_of_sets_in_trm: less-than-or-equal-to operation takes object sets that should be converted to predicates, but they were not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
			(match type_info.subseteq_symb with
			    Some subseteq_str ->
			      let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			      let new_trm = App(typed_subseteq_var,args) in
			      TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
			  | None ->
  			      let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			      let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			      let new_trm = App(typed_subseteq_var,args) in
			      let new_type_info = { type_info with subseteq_symb = Some subseteq_str } in
			      TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
		else TermApproximationNeeded
	    | _ ->
	      (match get_rid_of_sets_in_trm_list type_env type_info args with	    
		  TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		    let new_trm = App(Const LtEq,converted_args) in
		    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		| TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		    let new_trm = App(Const LtEq,converted_args) in
		    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		| TermListApproximationNeeded -> TermApproximationNeeded
		| NoTermListConversionNeeded -> NoTermConversionNeeded))
	else
	  failwith ("get_rid_of_sets_in_trm: the arguments of comparison should have the same type, but they don't in the following input: "^(PrintForm.string_of_form trm)^".\n")
    | App(Const LtEq,[TypedForm(arg,arg_ty) as typed_arg]) -> 
        (match arg_ty with
	    TypeApp(TypeSet,[ty]) -> 
	      if FormUtil.is_object_type ty then
		(match get_rid_of_sets_in_trm type_env type_info typed_arg with
		    TermExactlyConverted(new_var_types,updated_type_info,converted_typed_arg) ->
		      let new_typed_arg = overwritingly_attach_type converted_typed_arg predicate_on_objects_type in
		      (match updated_type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,[new_typed_arg]) in
			    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
			| None ->
			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_type_info = { updated_type_info with subseteq_symb = Some subseteq_str } in
			    let new_trm = App(typed_subseteq_var,[new_typed_arg]) in
			    TermExactlyConverted(new_var_types,new_type_info,new_trm))
		  | TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_typed_arg) ->
		      let new_typed_arg = overwritingly_attach_type converted_typed_arg predicate_on_objects_type in
		      (match updated_type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,[new_typed_arg]) in
			    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_type_info = { updated_type_info with subseteq_symb = Some subseteq_str } in
			    let new_trm = App(typed_subseteq_var,[new_typed_arg]) in
			    TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
		  | TermApproximationNeeded -> TermApproximationNeeded
		  | NoTermConversionNeeded ->
		      let _ = Util.warn ("get_rid_of_sets_in_trm: an argument of the subset relation has the set-of-object type, it should be rewritten to a predicate, but it was not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		      let new_typed_arg = overwritingly_attach_type arg predicate_on_objects_type in 
		      (match type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,[new_typed_arg]) in
			    TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
			| None ->
			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_type_info = { type_info with subseteq_symb = Some subseteq_str } in
			    let new_trm = App(typed_subseteq_var,[new_typed_arg]) in
			    TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
	      else TermApproximationNeeded
	  | _ -> 
	      (match get_rid_of_sets_in_trm type_env type_info typed_arg with	    
		  TermExactlyConverted(new_var_types,updated_type_info,converted_typed_arg) ->
		    let new_trm = App(Const LtEq,[converted_typed_arg]) in
		    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_typed_arg) ->
		    let new_trm = App(Const LtEq,[converted_typed_arg]) in
		    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		| x -> x ))
    | App(Const LtEq,[arg]) ->
        let type_env_as_list = mapVarType2typeEnv type_env in
	(match FormUtil.normalize_type (TypeReconstruct.get_type type_env_as_list arg) with
	    TypeApp(TypeSet,[ty]) -> 
	      if FormUtil.is_object_type ty then 
		(match get_rid_of_sets_in_trm type_env type_info arg with
		    TermExactlyConverted(new_var_types,updated_type_info,converted_arg) ->
		      (match updated_type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,[converted_arg]) in
			    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_type_info = { updated_type_info with subseteq_symb = Some subseteq_str } in
			    let new_trm = App(typed_subseteq_var,[converted_arg]) in
			    TermExactlyConverted(new_var_types,new_type_info,new_trm))
		  | TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_arg) ->
		      (match updated_type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,[converted_arg]) in
			    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_type_info = { updated_type_info with subseteq_symb = Some subseteq_str } in
			    let new_trm = App(typed_subseteq_var,[converted_arg]) in
			    TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
		  | TermApproximationNeeded -> TermApproximationNeeded
		  | NoTermConversionNeeded ->
	              let _ = Util.warn ("get_rid_of_sets_in_trm: less-than-or-equal-to operation takes object sets that should be converted to predicates, but they were not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		      (match type_info.subseteq_symb with
			  Some subseteq_str ->
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,[arg]) in
			    TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
			| None ->
  			    let subseteq_str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			    let typed_subseteq_var = FormUtil.mk_typedvar subseteq_str test_on_two_object_predicates_type in
			    let new_trm = App(typed_subseteq_var,[arg]) in
			    let new_type_info = { type_info with subseteq_symb = Some subseteq_str } in
			    TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
	      else TermApproximationNeeded
	  | _ -> 
	      (match get_rid_of_sets_in_trm type_env type_info arg with	    
		  TermExactlyConverted(new_var_types,updated_type_info,converted_arg) ->
		    let new_trm = App(Const LtEq,[converted_arg]) in
		    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_arg) ->
		    let new_trm = App(Const LtEq,[converted_arg]) in
		    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		| x -> x ))
    | App(Const Card, [TypedForm(arg,arg_ty) as typed_arg]) -> 
        (match FormUtil.normalize_type arg_ty with
	    TypeApp(TypeSet,[ty]) ->
	      if FormUtil.is_object_type ty then
		(match get_rid_of_sets_in_trm type_env type_info typed_arg with
		    TermExactlyConverted(new_var_types,updated_type_info,converted_typed_arg) ->
		      let new_typed_arg = overwritingly_attach_type converted_typed_arg predicate_on_objects_type in
		      (match updated_type_info.size_of_support_symb with
			  Some str -> 
			    let typed_var = FormUtil.mk_typedvar str size_of_support_of_objset_type in
			    let new_type_info = { updated_type_info with size_of_support_constraint_present=true } in
			    let new_trm = App(typed_var,[new_typed_arg]) in
			    TermExactlyConverted(new_var_types,new_type_info,new_trm)
			| None -> 
			    let str = Util.fresh_name (sizeOfSupport_prefix^(FormUtil.objset_str)) in
			    let typed_var = FormUtil.mk_typedvar str size_of_support_of_objset_type in
			    let new_trm = App(typed_var,[new_typed_arg]) in
			    let new_type_info = { updated_type_info with size_of_support_symb = Some str; size_of_support_constraint_present=true } in
			    TermExactlyConverted(new_var_types,new_type_info,new_trm))
		  | TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_typed_arg) ->
		      let new_typed_arg = overwritingly_attach_type converted_typed_arg predicate_on_objects_type in
		      (match updated_type_info.size_of_support_symb with
			  Some str -> 
			    let typed_var = FormUtil.mk_typedvar str size_of_support_of_objset_type in
			    let new_type_info = { updated_type_info with size_of_support_constraint_present=true } in
			    let new_trm = App(typed_var,[new_typed_arg]) in
			    TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm)
			| None -> 
			    let str = Util.fresh_name (sizeOfSupport_prefix^(FormUtil.objset_str)) in
			    let typed_var = FormUtil.mk_typedvar str size_of_support_of_objset_type in
			    let new_trm = App(typed_var,[new_typed_arg]) in
			    let new_type_info = { updated_type_info with size_of_support_symb = Some str; size_of_support_constraint_present=true } in
			    TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
		  | TermApproximationNeeded -> TermApproximationNeeded
		  | NoTermConversionNeeded -> 
	              let _ = Util.warn ("get_rid_of_sets_in_trm: cardinality operation takes an object set that should be converted to a predicate, but it has not been not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		      let new_typed_arg = overwritingly_attach_type arg predicate_on_objects_type in
		      (match type_info.size_of_support_symb with
			  Some str -> 
			    let typed_var = FormUtil.mk_typedvar str size_of_support_of_objset_type in
			    let new_type_info = { type_info with size_of_support_constraint_present=true } in
			    let new_trm = App(typed_var,[new_typed_arg]) in
			    TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)
			| None -> 
			    let str = Util.fresh_name (sizeOfSupport_prefix^(FormUtil.objset_str)) in
			    let typed_var = FormUtil.mk_typedvar str size_of_support_of_objset_type in
			    let new_trm = App(typed_var,[new_typed_arg]) in
			    let new_type_info = { type_info with size_of_support_symb = Some str; size_of_support_constraint_present=true } in
			    TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
	      else TermApproximationNeeded
	  | _ -> failwith ("get_rid_of_sets_in_trm: cardinality can be taken only of sets, so the following input is wrongly typed: "^(PrintForm.string_of_form trm)^".\n"))
    | App(Const Card,[arg]) ->
	let all_types = mapVarType2typeEnv type_env in
	(match FormUtil.normalize_type (TypeReconstruct.get_type all_types arg) with
	    TypeApp(TypeSet,[ty]) ->
	      if FormUtil.is_object_type ty then
		(match get_rid_of_sets_in_trm type_env type_info arg with
		    TermExactlyConverted(new_var_types,updated_type_info,converted_arg) ->
		      (match updated_type_info.size_of_support_symb with
			  Some str -> 
			    let typed_var = FormUtil.mk_typedvar str size_of_support_of_objset_type in
			    let new_type_info = { updated_type_info with size_of_support_constraint_present=true } in
			    let new_trm = App(typed_var,[converted_arg]) in
			    TermExactlyConverted(new_var_types,new_type_info,new_trm)
			| None -> 
			    let str = Util.fresh_name (sizeOfSupport_prefix^(FormUtil.objset_str)) in
			    let typed_var = FormUtil.mk_typedvar str size_of_support_of_objset_type in
			    let new_trm = App(typed_var,[converted_arg]) in
			    let new_type_info = { updated_type_info with size_of_support_symb = Some str; size_of_support_constraint_present=true } in
			    TermExactlyConverted(new_var_types,new_type_info,new_trm))
		  | TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_arg) ->
		      (match updated_type_info.size_of_support_symb with
			  Some str -> 
			    let typed_var = FormUtil.mk_typedvar str size_of_support_of_objset_type in
			    let new_type_info = { updated_type_info with size_of_support_constraint_present=true } in
			    let new_trm = App(typed_var,[converted_arg]) in
			    TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm)
			| None -> 
			    let str = Util.fresh_name (sizeOfSupport_prefix^(FormUtil.objset_str)) in
			    let typed_var = FormUtil.mk_typedvar str size_of_support_of_objset_type in
			    let new_trm = App(typed_var,[converted_arg]) in
			    let new_type_info = { updated_type_info with size_of_support_symb = Some str; size_of_support_constraint_present=true } in
			    TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
		  | TermApproximationNeeded -> TermApproximationNeeded
		  | NoTermConversionNeeded -> 
	              let _ = Util.warn ("get_rid_of_sets_in_trm: cardinality operation takes an object set that should be converted to a predicate, but it has not been not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		      (match type_info.size_of_support_symb with
			  Some str -> 
			    let typed_var = FormUtil.mk_typedvar str size_of_support_of_objset_type in
			    let new_type_info = { type_info with size_of_support_constraint_present=true } in
			    let new_trm = App(typed_var,[arg]) in
			    TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)
			| None -> 
			    let str = Util.fresh_name (sizeOfSupport_prefix^(FormUtil.objset_str)) in
			    let typed_var = FormUtil.mk_typedvar str size_of_support_of_objset_type in
			    let new_trm = App(typed_var,[arg]) in
			    let new_type_info = { type_info with size_of_support_symb = Some str; size_of_support_constraint_present=true } in
			    TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
	      else TermApproximationNeeded
	  | _ -> failwith ("get_rid_of_sets_in_trm: cardinalities can be taken only of sets, but in the following input the cardinality is taken of something else: "^(PrintForm.string_of_form trm)^".\n"))
    | App(Const Cardeq,[s;i]) ->
        let t1=App(Const Eq,[(FormUtil.mk_typedform(App(Const Card,[s]),FormUtil.mk_int_type)); (attach_type_if_not_attached i FormUtil.mk_int_type)]) in
	get_rid_of_sets_in_trm type_env type_info t1
    | App(Const Cardeq,[s]) ->
        let t1=App(Const Eq,[FormUtil.mk_typedform(App(Const Card,[s]),FormUtil.mk_int_type)]) in
	get_rid_of_sets_in_trm type_env type_info t1
    | App(Const Cardleq,[s;i]) ->
        let t1=App(Const LtEq,[(FormUtil.mk_typedform(App(Const Card,[s]),FormUtil.mk_int_type)); (attach_type_if_not_attached i FormUtil.mk_int_type)]) in
	get_rid_of_sets_in_trm type_env type_info t1
    | App(Const Cardleq,[s]) ->
        let t1=App(Const LtEq,[(FormUtil.mk_typedform(App(Const Card,[s]),FormUtil.mk_int_type))]) in
	get_rid_of_sets_in_trm type_env type_info t1
    | App(Const Cardgeq,[s;i]) ->
        let t1=App(Const GtEq,[(FormUtil.mk_typedform(App(Const Card,[s]),FormUtil.mk_int_type)); (attach_type_if_not_attached i FormUtil.mk_int_type)]) in
	get_rid_of_sets_in_trm type_env type_info t1
    | App(Const Cardgeq,[s]) ->
        let t1=App(Const GtEq,[FormUtil.mk_typedform(App(Const Card,[s]),FormUtil.mk_int_type)]) in
	get_rid_of_sets_in_trm type_env type_info t1
    | TypedForm(App(Const Cap,args),set_ty) ->
        (match FormUtil.normalize_type set_ty with
	    TypeApp(TypeSet,[ty]) -> 
	      if FormUtil.is_object_type ty then
		let no_of_args = List.length args in
		if no_of_args <= 0 then 
		  (match type_info.universalset_symb with
		      Some str ->
			let new_trm = FormUtil.mk_typedvar str predicate_on_objects_type in
			TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
		    | None ->
		        let str = Util.fresh_name (universalSet_prefix^(FormUtil.objset_str)) in
			let new_type_info = { type_info with universalset_symb = (Some str) } in
			let new_trm = FormUtil.mk_typedvar str predicate_on_objects_type in
			TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
		else if no_of_args = 1 then
		  let arg = List.hd args in
		  (match get_rid_of_sets_in_trm type_env type_info arg with
		      TermExactlyConverted(new_var_types,updated_type_info,converted_arg) ->
			let new_trm = overwritingly_attach_type converted_arg predicate_on_objects_type in
			TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		    | TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_arg) ->
			let new_trm = overwritingly_attach_type converted_arg predicate_on_objects_type in
			TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		    | TermApproximationNeeded -> TermApproximationNeeded
		    | NoTermConversionNeeded ->
		        let _ = Util.warn ("get_rid_of_sets_in_trm: intersection operation took a set that should be converted into a predicate, but is was not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		        let new_trm = overwritingly_attach_type arg predicate_on_objects_type in
			TermExactlyConverted(MapOfVars.empty,type_info,new_trm))
		else
		  (match get_rid_of_sets_in_trm_list type_env type_info args with
		      TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
         		let var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
			(try
			   let str = MapOfInts.find no_of_args updated_type_info.intersection_symb in
			   let typed_var = FormUtil.mk_typedvar str var_type in
			   let new_trm = FormUtil.mk_typedform (App(typed_var,converted_args),predicate_on_objects_type) in
			   TermExactlyConverted(new_var_types,updated_type_info,new_trm)
			 with Not_found ->
			   let str = Util.fresh_name (intersection_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
			   let typed_var = FormUtil.mk_typedvar str var_type in
			   let new_intersection_symb = MapOfInts.add no_of_args str updated_type_info.intersection_symb in
			   let new_type_info = {updated_type_info with intersection_symb = new_intersection_symb } in
			   let new_trm = FormUtil.mk_typedform (App(typed_var,converted_args),predicate_on_objects_type) in
			   TermExactlyConverted(new_var_types,new_type_info,new_trm))
		    | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		        let var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
		        (try
			   let str = MapOfInts.find no_of_args updated_type_info.intersection_symb in
			   let typed_var = FormUtil.mk_typedvar str var_type in
			   let new_trm = FormUtil.mk_typedform (App(typed_var,converted_args),predicate_on_objects_type) in
			   TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
			 with Not_found ->
			   let str = Util.fresh_name (intersection_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
			   let typed_var = FormUtil.mk_typedvar str var_type in
			   let new_intersection_symb = MapOfInts.add no_of_args str updated_type_info.intersection_symb in
			   let new_type_info = {updated_type_info with intersection_symb = new_intersection_symb } in
			   let new_trm = FormUtil.mk_typedform (App(typed_var,converted_args),predicate_on_objects_type) in
			   TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
		    | TermListApproximationNeeded -> TermApproximationNeeded
		    | NoTermListConversionNeeded ->
	                let _ = Util.warn ("get_rid_of_sets_in_trm: intersection operation took sets that should be converted to predicates, but they were not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
			let var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
			(try
			   let str = MapOfInts.find no_of_args type_info.intersection_symb in
			   let typed_var = FormUtil.mk_typedvar str var_type in
			   let new_trm = FormUtil.mk_typedform (App(typed_var,args),predicate_on_objects_type) in
			   TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
			 with Not_found ->
			   let str = Util.fresh_name (intersection_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
			   let typed_var = FormUtil.mk_typedvar str var_type in
			   let new_intersection_symb = MapOfInts.add no_of_args str type_info.intersection_symb in
			   let new_type_info = {type_info with intersection_symb = new_intersection_symb } in
			   let new_trm = FormUtil.mk_typedform (App(typed_var,args),predicate_on_objects_type) in
			   TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
	      else TermApproximationNeeded
	  | _ -> failwith ("get_rid_of_sets_in_trm: intersection should return a set, but it does not in the following input: "^(PrintForm.string_of_form trm)^".\n"))
    | App(Const Cap,[]) -> 
        TermApproximationNeeded
    | App(Const Cap,((arg::_) as args)) ->
	let type_env_as_list = mapVarType2typeEnv type_env in
	let get_ty = TypeReconstruct.get_type type_env_as_list in
        let is_of_objset_type f = is_objset_type (get_ty f) in
	if List.for_all is_of_objset_type args then
	  let no_of_args = List.length args in
	  if no_of_args = 1 then 
	    let result_of_getting_rid_of_sets_in_arg = get_rid_of_sets_in_trm type_env type_info arg in
	    (match result_of_getting_rid_of_sets_in_arg with
		TermExactlyConverted(_,_,_) | TermNonObjSetsProbablyLeft(_,_,_) | TermApproximationNeeded -> result_of_getting_rid_of_sets_in_arg
	      | NoTermConversionNeeded -> 
		  let _ = Util.warn ("get_rid_of_sets_in_trm: intersection operation took a set that should be converted into a predicate, but is was not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		  TermExactlyConverted(MapOfVars.empty,type_info,arg))
	  else
	    (match get_rid_of_sets_in_trm_list type_env type_info args with
		TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		  let var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
		  (try
		     let str = MapOfInts.find no_of_args updated_type_info.intersection_symb in
		     let typed_var = FormUtil.mk_typedvar str var_type in
		     let new_trm = App(typed_var,converted_args) in
		     TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		   with Not_found -> 
		     let str =  Util.fresh_name (intersection_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
		     let typed_var = FormUtil.mk_typedvar str var_type in
		     let new_intersection_symb = MapOfInts.add no_of_args str updated_type_info.intersection_symb in
		     let new_type_info = {updated_type_info with intersection_symb = new_intersection_symb } in
		     let new_trm = App(typed_var,converted_args) in
		     TermExactlyConverted(new_var_types,new_type_info,new_trm))
	      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		  let var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
		  (try
		     let str = MapOfInts.find no_of_args updated_type_info.intersection_symb in
		     let typed_var = FormUtil.mk_typedvar str var_type in
		     let new_trm = App(typed_var,converted_args) in
		     TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		   with Not_found -> 
		     let str =  Util.fresh_name (intersection_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
		     let typed_var = FormUtil.mk_typedvar str var_type in
		     let new_intersection_symb = MapOfInts.add no_of_args str updated_type_info.intersection_symb in
		     let new_type_info = {updated_type_info with intersection_symb = new_intersection_symb } in
		     let new_trm = App(typed_var,converted_args) in
		     TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
 	      | TermListApproximationNeeded -> TermApproximationNeeded
	      | NoTermListConversionNeeded ->
	          let _ = Util.warn ("get_rid_of_sets_in_trm: intersection operation took sets that should be converted to predicates, but they were not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		  let var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
		  (try
		     let str = MapOfInts.find no_of_args type_info.intersection_symb in
		     let typed_var = FormUtil.mk_typedvar str var_type in
		     let new_trm = App(typed_var,args) in
		     TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
		   with Not_found -> 
		     let str =  Util.fresh_name (intersection_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
		     let typed_var = FormUtil.mk_typedvar str var_type in
		     let new_intersection_symb = MapOfInts.add no_of_args str type_info.intersection_symb in
		     let new_type_info = {type_info with intersection_symb = new_intersection_symb } in
		     let new_trm = App(typed_var,args) in
		     TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
	else TermApproximationNeeded
    | TypedForm(App(Const Cup,args),set_ty) ->
        (match FormUtil.normalize_type set_ty with
	    TypeApp(TypeSet,[ty]) ->
	      if FormUtil.is_object_type ty then
		let no_of_args = List.length args in
		if no_of_args<=0 then
		  (match type_info.emptyset_symb with
		      Some str ->
			let new_trm = FormUtil.mk_typedvar str predicate_on_objects_type in
			TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
		    | None ->
		        let str = Util.fresh_name (emptySet_prefix^(FormUtil.objset_str)) in
			let new_type_info = { type_info with emptyset_symb = (Some str) } in
			let new_trm = FormUtil.mk_typedvar str predicate_on_objects_type in
			TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
		else if no_of_args = 1 then
		  let arg = List.hd args in
		  (match get_rid_of_sets_in_trm type_env type_info arg with
		      TermExactlyConverted(new_var_types,updated_type_info,converted_arg) ->
			let new_trm = overwritingly_attach_type converted_arg predicate_on_objects_type in
			TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		    | TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_arg) ->
			let new_trm = overwritingly_attach_type converted_arg predicate_on_objects_type in
			TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		    | TermApproximationNeeded -> TermApproximationNeeded
		    | NoTermConversionNeeded ->
		        let _ = Util.warn ("get_rid_of_sets_in_trm: union operation took a set that should be converted into a predicate, but is was not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
			let new_trm = overwritingly_attach_type arg predicate_on_objects_type in
			TermExactlyConverted(MapOfVars.empty,type_info,new_trm))
		else 
		  (match get_rid_of_sets_in_trm_list type_env type_info args with
		      TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
         		let var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
			(try
			   let str = MapOfInts.find no_of_args updated_type_info.union_symb in
			   let typed_var = FormUtil.mk_typedvar str var_type in
			   let new_trm = FormUtil.mk_typedform (App(typed_var,converted_args),predicate_on_objects_type) in
			   TermExactlyConverted(new_var_types,updated_type_info,new_trm)
			 with Not_found ->
			   let str = Util.fresh_name (union_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
			   let typed_var = FormUtil.mk_typedvar str var_type in
			   let new_union_symb = MapOfInts.add no_of_args str updated_type_info.union_symb in
			   let new_type_info = {updated_type_info with union_symb = new_union_symb } in
			   let new_trm = FormUtil.mk_typedform (App(typed_var,converted_args),predicate_on_objects_type) in
			   TermExactlyConverted(new_var_types,new_type_info,new_trm))
		    | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		        let var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
		        (try
			   let str = MapOfInts.find no_of_args updated_type_info.union_symb in
			   let typed_var = FormUtil.mk_typedvar str var_type in
			   let new_trm = FormUtil.mk_typedform (App(typed_var,converted_args),predicate_on_objects_type) in
			   TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
			 with Not_found ->
			   let str = Util.fresh_name (union_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
			   let typed_var = FormUtil.mk_typedvar str var_type in
			   let new_union_symb = MapOfInts.add no_of_args str updated_type_info.union_symb in
			   let new_type_info = {updated_type_info with union_symb = new_union_symb } in
			   let new_trm = FormUtil.mk_typedform (App(typed_var,converted_args),predicate_on_objects_type) in
			   TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
		    | TermListApproximationNeeded -> TermApproximationNeeded
		    | NoTermListConversionNeeded ->
	                let _ = Util.warn ("get_rid_of_sets_in_trm: union operation took sets that should be converted to predicates, but they were not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
			let var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
			(try
			   let str = MapOfInts.find no_of_args type_info.union_symb in
			   let typed_var = FormUtil.mk_typedvar str var_type in
			   let new_trm = FormUtil.mk_typedform (App(typed_var,args),predicate_on_objects_type) in
			   TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
			 with Not_found ->
			   let str = Util.fresh_name (union_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
			   let typed_var = FormUtil.mk_typedvar str var_type in
			   let new_union_symb = MapOfInts.add no_of_args str type_info.union_symb in
			   let new_type_info = {type_info with union_symb = new_union_symb } in
			   let new_trm = FormUtil.mk_typedform (App(typed_var,args),predicate_on_objects_type) in
			   TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
		else TermApproximationNeeded
	  | _ -> failwith ("get_rid_of_sets_in_trm: intersection should return a set, but it does not in the following input: "^(PrintForm.string_of_form trm)^".\n"))
    | App(Const Cup,[]) -> 
        TermApproximationNeeded
    | App(Const Cup,((arg::_) as args)) ->
	let all_types = mapVarType2typeEnv type_env in
	let get_ty = TypeReconstruct.get_type all_types in
        let is_of_objset_type f = is_objset_type (get_ty f) in
	if List.for_all is_of_objset_type args then
	  let no_of_args = List.length args in
	  if no_of_args = 1 then 
	    let result_of_getting_rid_of_sets_in_arg = get_rid_of_sets_in_trm type_env type_info arg in
	    (match result_of_getting_rid_of_sets_in_arg with
		TermExactlyConverted(_,_,_) | TermNonObjSetsProbablyLeft(_,_,_) | TermApproximationNeeded -> result_of_getting_rid_of_sets_in_arg
	      | NoTermConversionNeeded -> 
		  let _ = Util.warn ("get_rid_of_sets_in_trm: intersection operation took a set that should be converted into a predicate, but is was not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		  TermExactlyConverted(MapOfVars.empty,type_info,arg))
	  else
	    (match get_rid_of_sets_in_trm_list type_env type_info args with
		TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		  let var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
		  (try
		     let str = MapOfInts.find no_of_args updated_type_info.union_symb in
		     let typed_var = FormUtil.mk_typedvar str var_type in
		     let new_trm = App(typed_var,converted_args) in
		     TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		   with Not_found -> 
		     let str = Util.fresh_name (union_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
		     let typed_var = FormUtil.mk_typedvar str var_type in
		     let new_union_symb = MapOfInts.add no_of_args str updated_type_info.union_symb in
		     let new_type_info = {updated_type_info with union_symb = new_union_symb } in
		     let new_trm = App(typed_var,converted_args) in
		     TermExactlyConverted(new_var_types,new_type_info,new_trm))
	      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		  let var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
		  (try
		     let str = MapOfInts.find no_of_args updated_type_info.union_symb in
		     let typed_var = FormUtil.mk_typedvar str var_type in
		     let new_trm = App(typed_var,converted_args) in
		     TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		   with Not_found -> 
		     let str =  Util.fresh_name (union_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
		     let typed_var = FormUtil.mk_typedvar str var_type in
		     let new_union_symb = MapOfInts.add no_of_args str updated_type_info.union_symb in
		     let new_type_info = {updated_type_info with union_symb = new_union_symb } in
		     let new_trm = App(typed_var,converted_args) in
		     TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm))
 	      | TermListApproximationNeeded -> TermApproximationNeeded
	      | NoTermListConversionNeeded ->
	          let _ = Util.warn ("get_rid_of_sets_in_trm: union operation took sets that should be converted to predicates, but they were not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		  let var_type = FormUtil.mk_fun_type (make_list_of_identical_items predicate_on_objects_type no_of_args) predicate_on_objects_type in
		  (try
		     let str = MapOfInts.find no_of_args type_info.union_symb in
		     let typed_var = FormUtil.mk_typedvar str var_type in
		     let new_trm = App(typed_var,args) in
		     TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
		   with Not_found -> 
		     let str =  Util.fresh_name (union_prefix^(string_of_int no_of_args)^"_"^(FormUtil.objset_str)) in
		     let typed_var = FormUtil.mk_typedvar str var_type in
		     let new_union_symb = MapOfInts.add no_of_args str type_info.union_symb in
		     let new_type_info = {type_info with union_symb = new_union_symb } in
		     let new_trm = App(typed_var,args) in
		     TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm)))
	else TermApproximationNeeded
    | TypedForm(App(Const Diff,((_::_) as args)),set_ty) ->
        if is_objset_type set_ty then
	  (match get_rid_of_sets_in_trm_list type_env type_info args with
	      TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.difference_symb with
		      Some str -> (str,updated_type_info)
		    | None -> 
		        let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with difference_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		let new_trm = FormUtil.mk_typedform((App(typed_diff_var,converted_args)),predicate_on_objects_type) in
		TermExactlyConverted(new_var_types,new_type_info,new_trm)
	    | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.difference_symb with
		      Some str -> (str,updated_type_info)
		    | None -> 
		        let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with difference_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		let new_trm = FormUtil.mk_typedform((App(typed_diff_var,converted_args)),predicate_on_objects_type) in
		TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm)
	    | TermListApproximationNeeded -> TermApproximationNeeded
	    | NoTermListConversionNeeded ->
	        let _ = Util.warn ("get_rid_of_sets_in_trm: arguments of set difference have set-of-object type, they should have been rewritten to predicates, but they have not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		let (str,new_type_info) =
		  (match type_info.difference_symb with
		      Some str -> (str,type_info)
		    | None -> 
		        let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			let new_type_info = { type_info with difference_symb = (Some str) } in
			(str,new_type_info)) in
		let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		let new_trm = FormUtil.mk_typedform((App(typed_diff_var,args)),predicate_on_objects_type) in
		TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
	else TermApproximationNeeded
    | App(Const Diff,([TypedForm(_,set_ty);_] as args)) | App(Const Diff,([_;TypedForm(_,set_ty)] as args)) | App(Const Diff,([TypedForm(_,set_ty)] as args)) ->
        if is_objset_type set_ty then
	  (match get_rid_of_sets_in_trm_list type_env type_info args with
	      TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.difference_symb with
		      Some str -> (str,updated_type_info)
		    | None -> 
		        let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with difference_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermExactlyConverted(new_var_types,new_type_info,new_trm)
	    | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.difference_symb with
		      Some str -> (str,updated_type_info)
		    | None -> 
		        let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with difference_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm)
	    | TermListApproximationNeeded -> TermApproximationNeeded
	    | NoTermListConversionNeeded ->
	        let _ = Util.warn ("get_rid_of_sets_in_trm: arguments of set difference have set-of-object type, they should have been rewritten to predicates, but they have not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		let (str,new_type_info) =
		  (match type_info.difference_symb with
		      Some str -> (str,type_info)
		    | None -> 
		        let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			let new_type_info = { type_info with difference_symb = (Some str) } in
			(str,new_type_info)) in
		let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		let new_trm = App(typed_diff_var,args) in
		TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
	else TermApproximationNeeded
    | App(Const Diff,((_::_) as args)) ->
        let type_env_as_list = mapVarType2typeEnv type_env in
	let get_ty = TypeReconstruct.get_type type_env_as_list in
	let is_os f = is_objset_type (get_ty f) in
	if List.for_all is_os args then
	  (match get_rid_of_sets_in_trm_list type_env type_info args with
	      TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.difference_symb with
		      Some str -> (str,updated_type_info)
		    | None -> 
		        let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with difference_symb = (Some str) })) in
		let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermExactlyConverted(new_var_types,new_type_info,new_trm)
	    | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.difference_symb with
		      Some str -> (str,updated_type_info)
		    | None -> 
		        let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with difference_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm)
	    | TermListApproximationNeeded -> TermApproximationNeeded
	    | NoTermListConversionNeeded ->
	        let _ = Util.warn ("get_rid_of_sets_in_trm: arguments of set difference have set-of-object type, they should have been rewritten to predicates, but they have not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		let (str,new_type_info) =
		  (match type_info.difference_symb with
		      Some str -> (str,type_info)
		    | None -> 
		        let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			let new_type_info = { type_info with difference_symb = (Some str) } in
			(str,new_type_info)) in
		let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		let new_trm = App(typed_diff_var,args) in
		TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
	else TermApproximationNeeded
    | App(Const Subseteq,(([TypedForm(_,set_ty);_]) as args)) | App(Const Subseteq,(([_;TypedForm(_,set_ty)]) as args)) | App(Const Subseteq,(([TypedForm(_,set_ty)]) as args)) ->
        if is_objset_type set_ty then
	  (match get_rid_of_sets_in_trm_list type_env type_info args with
	      TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.subseteq_symb with
		      Some str -> (str,updated_type_info)
		    | None ->
		        let str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with subseteq_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str test_on_two_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermExactlyConverted(new_var_types,new_type_info,new_trm)
	    | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.subseteq_symb with
		      Some str -> (str,updated_type_info)
		    | None ->
		        let str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with subseteq_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str test_on_two_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm)
	    | TermListApproximationNeeded -> TermApproximationNeeded
	    | NoTermListConversionNeeded ->
	        let _ = Util.warn ("get_rid_of_sets_in_trm: arguments of set inclusion have set-of-object type, they should have been rewritten to predicates, but they have not been rewritten in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		let (str,new_type_info) =
		  (match type_info.subseteq_symb with
		      Some str -> (str,type_info)
		    | None ->
		        let str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			(str, { type_info with subseteq_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str test_on_two_object_predicates_type in
		let new_trm = App(typed_diff_var,args) in
		TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
	else TermApproximationNeeded
    | App(Const Subseteq,((_::_) as args)) ->
        let all_types = mapVarType2typeEnv type_env in
	let get_ty = TypeReconstruct.get_type all_types in
	let is_os f = is_objset_type (get_ty f) in
	if List.for_all is_os args then
	  (match get_rid_of_sets_in_trm_list type_env type_info args with
	      TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.subseteq_symb with
		      Some str -> (str,updated_type_info)
		    | None ->
		        let str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with subseteq_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str test_on_two_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermExactlyConverted(new_var_types,new_type_info,new_trm)
	    | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.subseteq_symb with
		      Some str -> (str,updated_type_info)
		    | None ->
		        let str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with subseteq_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str test_on_two_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm)
	    | TermListApproximationNeeded -> TermApproximationNeeded
	    | NoTermListConversionNeeded ->
	        let _ = Util.warn ("get_rid_of_sets_in_trm: arguments of set inclusion have set-of-object type, they should have been rewritten to predicates, but they have not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		let (str,new_type_info) =
		  (match type_info.subseteq_symb with
		      Some str -> (str,type_info)
		    | None ->
		        let str = Util.fresh_name (subseteq_prefix^(FormUtil.objset_str)) in
			(str, { type_info with subseteq_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str test_on_two_object_predicates_type in
		let new_trm = App(typed_diff_var,args) in
		TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
	else TermApproximationNeeded
    | App(Const Subset,(([TypedForm(_,set_ty);_]) as args)) | App(Const Subset,(([_;TypedForm(_,set_ty)]) as args)) | App(Const Subset,(([TypedForm(_,set_ty)]) as args)) ->
        if is_objset_type set_ty then
	  (match get_rid_of_sets_in_trm_list type_env type_info args with
	      TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.strictSubset_symb with
		      Some str -> (str,updated_type_info)
		    | None ->
		        let str = Util.fresh_name (strictSubset_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with strictSubset_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str test_on_two_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermExactlyConverted(new_var_types,new_type_info,new_trm)
	    | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.strictSubset_symb with
		      Some str -> (str,updated_type_info)
		    | None ->
		        let str = Util.fresh_name (strictSubset_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with strictSubset_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str test_on_two_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm)
	    | TermListApproximationNeeded -> TermApproximationNeeded
	    | NoTermListConversionNeeded ->
	        let _ = Util.warn ("get_rid_of_sets_in_trm: arguments of set inclusion have set-of-object type, they should have been rewritten to predicates, but they have not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		let (str,new_type_info) =
		  (match type_info.strictSubset_symb with
		      Some str -> (str,type_info)
		    | None ->
		        let str = Util.fresh_name (strictSubset_prefix^(FormUtil.objset_str)) in
			(str, { type_info with strictSubset_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str test_on_two_object_predicates_type in
		let new_trm = App(typed_diff_var,args) in
		TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
	else TermApproximationNeeded
    | App(Const Subset,((_::_) as args)) ->
        let all_types = mapVarType2typeEnv type_env in
	let get_ty = TypeReconstruct.get_type all_types in
	let is_os f = is_objset_type (get_ty f) in
	if List.for_all is_os args then
	  (match get_rid_of_sets_in_trm_list type_env type_info args with
	      TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.strictSubset_symb with
		      Some str -> (str,updated_type_info)
		    | None ->
		        let str = Util.fresh_name (strictSubset_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with strictSubset_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str test_on_two_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermExactlyConverted(new_var_types,new_type_info,new_trm)
	    | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.strictSubset_symb with
		      Some str -> (str,updated_type_info)
		    | None ->
		        let str = Util.fresh_name (strictSubset_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with strictSubset_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str test_on_two_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm)
	    | TermListApproximationNeeded -> TermApproximationNeeded
	    | NoTermListConversionNeeded ->
	        let _ = Util.warn ("get_rid_of_sets_in_trm: arguments of set inclusion have set-of-object type, they should have been rewritten to predicates, but they have not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		let (str,new_type_info) =
		  (match type_info.strictSubset_symb with
		      Some str -> (str,type_info)
		    | None ->
		        let str = Util.fresh_name (strictSubset_prefix^(FormUtil.objset_str)) in
			(str, { type_info with strictSubset_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str test_on_two_object_predicates_type in
		let new_trm = App(typed_diff_var,args) in
		TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
	else TermApproximationNeeded
    | TypedForm(App(Const Minus,((_::_) as args)),res_ty) ->
        (match FormUtil.normalize_type res_ty with
	    TypeApp(TypeSet,[ty]) ->
	      if FormUtil.is_object_type ty then
		(match get_rid_of_sets_in_trm_list type_env type_info args with
		    TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		      let (str,new_type_info) =
			(match updated_type_info.difference_symb with
			    Some str -> (str,updated_type_info)
			  | None -> 
		            let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			    (str, { updated_type_info with difference_symb = (Some str) } )) in
		      let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		      let new_trm = FormUtil.mk_typedform((App(typed_diff_var,converted_args)),predicate_on_objects_type) in
		      TermExactlyConverted(new_var_types,new_type_info,new_trm)
		  | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
                      let (str,new_type_info) =
			(match updated_type_info.difference_symb with
			    Some str -> (str,updated_type_info)
			  | None -> 
		            let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			    (str, { updated_type_info with difference_symb = (Some str) } )) in
		      let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		      let new_trm = FormUtil.mk_typedform((App(typed_diff_var,converted_args)),predicate_on_objects_type) in
		      TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm)
		  | TermListApproximationNeeded -> TermApproximationNeeded
		  | NoTermListConversionNeeded ->
	              let _ = Util.warn ("get_rid_of_sets_in_trm: arguments of set difference have set-of-object type, they should have been rewritten to predicates, but they have not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		      let (str,new_type_info) =
			(match type_info.difference_symb with
			    Some str -> (str,type_info)
			  | None -> 
		              let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			      let new_type_info = { type_info with difference_symb = (Some str) } in
			      (str,new_type_info)) in
		      let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		      let new_trm = FormUtil.mk_typedform((App(typed_diff_var,args)),predicate_on_objects_type) in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
	      else TermApproximationNeeded
	  | _ ->
	      (match try_get_rid_of_sets_in_type res_ty with
		  TypeExactlyConverted new_res_ty -> 
		    (match get_rid_of_sets_in_trm_list type_env type_info args with
			TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
			  let new_trm = FormUtil.mk_typedform(App(Const Minus,converted_args),new_res_ty) in
			  TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
			  let new_trm = FormUtil.mk_typedform(App(Const Minus,converted_args),new_res_ty) in
			  TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		      | TermListApproximationNeeded -> TermApproximationNeeded
		      | NoTermListConversionNeeded ->
	                  let _ = Util.warn ("get_rid_of_sets_in_trm: the type of the result of difference has been converted, but the arguments have not been converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
			  let new_trm = FormUtil.mk_typedform(App(Const Minus,args),new_res_ty) in
			  TermExactlyConverted(MapOfVars.empty,type_info,new_trm))
		| NonObjSetTypesPresent new_res_ty ->
		    (match get_rid_of_sets_in_trm_list type_env type_info args with
			TermListExactlyConverted(new_var_types,updated_type_info,converted_args)
		      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
			  let new_trm = FormUtil.mk_typedform(App(Const Minus,converted_args),new_res_ty) in
			  TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		      | TermListApproximationNeeded -> TermApproximationNeeded
		      | NoTermListConversionNeeded ->
	                  let _ = Util.warn ("get_rid_of_sets_in_trm: the type of the result of difference has been converted, but the arguments have not been converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
			  let new_trm = FormUtil.mk_typedform(App(Const Minus,args),new_res_ty) in
			  TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,new_trm))
		| NoTypeConversionNeeded ->
		    (match get_rid_of_sets_in_trm_list type_env type_info args with
			TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
			  let new_trm = FormUtil.mk_typedform(App(Const Minus,converted_args),res_ty) in
			  TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
			  let new_trm = FormUtil.mk_typedform(App(Const Minus,converted_args),res_ty) in
			  TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		      | TermListApproximationNeeded -> TermApproximationNeeded
		      | NoTermListConversionNeeded -> NoTermConversionNeeded)))
    | App(Const Minus,([TypedForm(_,arg_ty);_] as args)) | App(Const Minus,([_;TypedForm(_,arg_ty)] as args)) | App(Const Minus,([TypedForm(_,arg_ty)] as args)) ->
        (match arg_ty with
	    TypeApp(TypeSet,[ty]) ->
	      if FormUtil.is_object_type ty then
		(match get_rid_of_sets_in_trm_list type_env type_info args with
		    TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		      let (str,new_type_info) =
			(match updated_type_info.difference_symb with
			    Some str -> (str,updated_type_info)
			  | None -> 
		            let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			    (str, { updated_type_info with difference_symb = (Some str) } )) in
		      let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		      let new_trm = App(typed_diff_var,converted_args) in
		      TermExactlyConverted(new_var_types,new_type_info,new_trm)
		  | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
                      let (str,new_type_info) =
			(match updated_type_info.difference_symb with
			    Some str -> (str,updated_type_info)
			  | None -> 
		            let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			    (str, { updated_type_info with difference_symb = (Some str) } )) in
		      let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		      let new_trm = App(typed_diff_var,converted_args) in
		      TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm)
		  | TermListApproximationNeeded -> TermApproximationNeeded
		  | NoTermListConversionNeeded ->
	              let _ = Util.warn ("get_rid_of_sets_in_trm: arguments of set difference have set-of-object type, they should have been rewritten to predicates, but they have not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		      let (str,new_type_info) =
			(match type_info.difference_symb with
			    Some str -> (str,type_info)
			  | None -> 
		              let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			      let new_type_info = { type_info with difference_symb = (Some str) } in
			      (str,new_type_info)) in
		      let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		      let new_trm = App(typed_diff_var,args) in
		      TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
	      else TermApproximationNeeded
	  | _ -> 
	      (match try_get_rid_of_sets_in_type arg_ty with
		  TypeExactlyConverted _ -> 
		    (match get_rid_of_sets_in_trm_list type_env type_info args with
			TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
			  let new_trm = App(Const Minus,converted_args) in
			  TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
			  let new_trm = App(Const Minus,converted_args) in
			  TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		      | TermListApproximationNeeded -> TermApproximationNeeded
		      | NoTermListConversionNeeded ->
	                  let _ = Util.warn ("get_rid_of_sets_in_trm: the type of the result of difference has been converted, but the arguments have not been converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
			  TermExactlyConverted(MapOfVars.empty,type_info,trm))
		| NonObjSetTypesPresent _ ->
		    (match get_rid_of_sets_in_trm_list type_env type_info args with
			TermListExactlyConverted(new_var_types,updated_type_info,converted_args)
		      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		          let new_trm = App(Const Minus,converted_args) in
			  TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		      | TermListApproximationNeeded -> TermApproximationNeeded
		      | NoTermListConversionNeeded ->
	                  let _ = Util.warn ("get_rid_of_sets_in_trm: the type of the result of difference has been converted, but the arguments have not been converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
			  TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,trm))
		| NoTypeConversionNeeded ->
		    (match get_rid_of_sets_in_trm_list type_env type_info args with
			TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
			  let new_trm = App(Const Minus,converted_args) in
			  TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
			  let new_trm = App(Const Minus,converted_args) in
			  TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		      | TermListApproximationNeeded -> TermApproximationNeeded
		      | NoTermListConversionNeeded -> NoTermConversionNeeded)))
    | App(Const Minus,((_::_) as args)) ->
        let all_types = mapVarType2typeEnv type_env in
	let get_ty = TypeReconstruct.get_type all_types in
	let (objset_found,set_found) = List.fold_right
	  (fun a (sofar_objset_found,sofar_set_found) -> 
	    if sofar_objset_found then (sofar_objset_found,sofar_set_found)
	    else
	      match get_ty a with
		  TypeApp(TypeSet,[ty]) -> 
		    if FormUtil.is_object_type ty then (true,true)
		    else (false,true)
		| _ -> (false,sofar_set_found)
	  ) args (false,false) in
	if objset_found then
	  (match get_rid_of_sets_in_trm_list type_env type_info args with
	      TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.difference_symb with
		      Some str -> (str,updated_type_info)
		    | None -> 
		        let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with difference_symb = (Some str) })) in
		let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermExactlyConverted(new_var_types,new_type_info,new_trm)
	    | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		let (str,new_type_info) =
		  (match updated_type_info.difference_symb with
		      Some str -> (str,updated_type_info)
		    | None -> 
		        let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			(str, { updated_type_info with difference_symb = (Some str) } )) in
		let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		let new_trm = App(typed_diff_var,converted_args) in
		TermNonObjSetsProbablyLeft(new_var_types,new_type_info,new_trm)
	    | TermListApproximationNeeded -> TermApproximationNeeded
	    | NoTermListConversionNeeded ->
	        let _ = Util.warn ("get_rid_of_sets_in_trm: arguments of set difference have set-of-object type, they should have been rewritten to predicates, but they have not in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		let (str,new_type_info) =
		  (match type_info.difference_symb with
		      Some str -> (str,type_info)
		    | None -> 
		        let str = Util.fresh_name (difference_prefix^(FormUtil.objset_str)) in
			let new_type_info = { type_info with difference_symb = (Some str) } in
			(str,new_type_info)) in
		let typed_diff_var = FormUtil.mk_typedvar str operator_on_object_predicates_type in
		let new_trm = App(typed_diff_var,args) in
		TermExactlyConverted(MapOfVars.empty,new_type_info,new_trm))
	else if set_found then TermApproximationNeeded
	else
	  (match get_rid_of_sets_in_trm_list type_env type_info args with
	      TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		let new_trm = App(Const Minus,converted_args) in
		TermExactlyConverted(new_var_types,updated_type_info,new_trm)
	    | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
	        let new_trm = App(Const Minus,converted_args) in
		TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
	    | TermListApproximationNeeded -> TermApproximationNeeded
	    | NoTermListConversionNeeded -> NoTermConversionNeeded)
    | TypedForm(App(Const FiniteSetConst,[arg]),ty) ->
        (match FormUtil.normalize_type ty with
	      TypeApp(TypeSet,[ty1]) ->
		(match try_get_rid_of_sets_in_type ty1 with
		    TypeExactlyConverted new_ty1 ->
		      (match get_rid_of_sets_in_trm type_env type_info arg with
			  TermExactlyConverted(new_var_types,updated_type_info,converted_arg) ->
			    let trm_ty = FormUtil.mk_fun_type [new_ty1] FormUtil.mk_bool_type in
			    let new_trm = TypedForm(App(Const Eq,[converted_arg]),trm_ty) in
			    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
			| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_arg) ->
			    let trm_ty = FormUtil.mk_fun_type [new_ty1] FormUtil.mk_bool_type in
		            let new_trm = TypedForm(App(Const Eq,[converted_arg]),trm_ty) in
			    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
			| TermApproximationNeeded -> TermApproximationNeeded
			| NoTermConversionNeeded ->
			    let trm_ty = FormUtil.mk_fun_type [new_ty1] FormUtil.mk_bool_type in
			    let new_trm = TypedForm(App(Const Eq,[arg]),trm_ty) in
			    TermExactlyConverted(MapOfVars.empty,type_info,new_trm))
		  | NonObjSetTypesPresent new_ty1 ->
		      (match get_rid_of_sets_in_trm type_env type_info arg with
			  TermExactlyConverted(new_var_types,updated_type_info,converted_arg)
			| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_arg) ->
			    let trm_ty = FormUtil.mk_fun_type [new_ty1] FormUtil.mk_bool_type in
		            let new_trm = TypedForm(App(Const Eq,[converted_arg]),trm_ty) in
			    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
			| TermApproximationNeeded -> TermApproximationNeeded
			| NoTermConversionNeeded ->
			    let trm_ty = FormUtil.mk_fun_type [new_ty1] FormUtil.mk_bool_type in
			    let new_trm = TypedForm(App(Const Eq,[arg]),trm_ty) in
			    TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,new_trm))
		  | NoTypeConversionNeeded ->
		      (match get_rid_of_sets_in_trm type_env type_info arg with
			  TermExactlyConverted(new_var_types,updated_type_info,converted_arg) ->
			    let trm_ty = FormUtil.mk_fun_type [ty1] FormUtil.mk_bool_type in
			    let new_trm = TypedForm(App(Const Eq,[converted_arg]),trm_ty) in
			    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
			| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_arg) ->
			    let trm_ty = FormUtil.mk_fun_type [ty1] FormUtil.mk_bool_type in
		            let new_trm = TypedForm(App(Const Eq,[converted_arg]),trm_ty) in
			    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
			| TermApproximationNeeded -> TermApproximationNeeded
			| NoTermConversionNeeded ->
			    let trm_ty = FormUtil.mk_fun_type [ty1] FormUtil.mk_bool_type in
			    let new_trm = TypedForm(App(Const Eq,[arg]),trm_ty) in
			    TermExactlyConverted(MapOfVars.empty,type_info,new_trm)))
	    | _ -> failwith ("get_rid_of_sets_in_trm: the singleton should be set-typed, but it has a non-set type in the following input: "^(PrintForm.string_of_form trm)^".\n"))
    | App(Const FiniteSetConst,[TypedForm(arg,ty) as typed_arg]) ->
        (match try_get_rid_of_sets_in_type ty with
	    TypeExactlyConverted _ ->
	      (match get_rid_of_sets_in_trm type_env type_info typed_arg with
		  TermExactlyConverted(new_var_types,updated_type_info,converted_arg) ->
		    let new_trm = App(Const Eq,[converted_arg]) in
		    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_arg) ->
		    let new_trm = App(Const Eq,[converted_arg]) in
		    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		| TermApproximationNeeded -> TermApproximationNeeded
		| NoTermConversionNeeded ->
		    let _ = Util.warn ("get_rid_of_sets_in_trm: the type was converted, but the corresponding term was not, which is strange, in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		    let new_trm = App(Const Eq,[typed_arg]) in
		    TermExactlyConverted(MapOfVars.empty,type_info,new_trm))
	  | NonObjSetTypesPresent _ ->
	      (match get_rid_of_sets_in_trm type_env type_info typed_arg with
		  TermExactlyConverted(new_var_types,updated_type_info,converted_arg)
		| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_arg) ->
		   let new_trm = App(Const Eq,[converted_arg]) in
		   TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		| TermApproximationNeeded -> TermApproximationNeeded
		| NoTermConversionNeeded ->
		    let _ = Util.warn ("get_rid_of_sets_in_trm: the type was incompletely converted, but the corresponding term was not converted at all, which is strange, in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		    let new_trm = App(Const Eq,[typed_arg]) in
		    TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,new_trm))
	  | NoTypeConversionNeeded ->
	      (match get_rid_of_sets_in_trm type_env type_info arg with
		  TermExactlyConverted(new_var_types,updated_type_info,converted_arg) ->
		    let new_trm = App(Const Eq,[converted_arg]) in
		    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_arg) ->
		    let new_trm = App(Const Eq,[converted_arg]) in
		    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		| TermApproximationNeeded -> TermApproximationNeeded
		| NoTermConversionNeeded ->
		    let new_trm = App(Const Eq,[typed_arg]) in
		    TermExactlyConverted(MapOfVars.empty,type_info,new_trm)))
    | TypedForm(App(Const FiniteSetConst,args),set_ty) ->
        (match FormUtil.normalize_type set_ty with
	    TypeApp(TypeSet,[ty]) ->
	      (match try_get_rid_of_sets_in_type ty with
		  TypeExactlyConverted converted_ty ->
		    (match get_rid_of_sets_in_trm_list type_env type_info args with
			TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
			  let new_trm_ty = FormUtil.mk_fun_type [converted_ty] FormUtil.mk_bool_type in
			  let var_name = Util.fresh_name "v" in
			  let typed_var = FormUtil.mk_typedvar var_name converted_ty in
			  let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) converted_args) in
			  let new_trm = FormUtil.mk_typedform (Binder(Lambda,[(var_name,converted_ty)],comparison), new_trm_ty) in
			  TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
			  let new_trm_ty = FormUtil.mk_fun_type [converted_ty] FormUtil.mk_bool_type in
			  let var_name = Util.fresh_name "v" in
			  let typed_var = FormUtil.mk_typedvar var_name converted_ty in
			  let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) converted_args) in
			  let new_trm = FormUtil.mk_typedform (Binder(Lambda,[(var_name,converted_ty)],comparison), new_trm_ty) in
			  TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		      | TermListApproximationNeeded -> TermApproximationNeeded
		      | NoTermListConversionNeeded ->
			  let _ = Util.warn ("get_rid_of_sets_in_trm: in the following input, the type was converted, but the terms were not, which is strange: "^(PrintForm.string_of_form trm)^".\n") in
			  let new_trm_ty = FormUtil.mk_fun_type [converted_ty] FormUtil.mk_bool_type in
			  let var_name = Util.fresh_name "v" in
			  let typed_var = FormUtil.mk_typedvar var_name converted_ty in
			  let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) args) in
			  let new_trm = FormUtil.mk_typedform (Binder(Lambda,[(var_name,converted_ty)],comparison), new_trm_ty) in
			  TermExactlyConverted(MapOfVars.empty,type_info,new_trm))
		| NonObjSetTypesPresent converted_ty -> 
		    (match get_rid_of_sets_in_trm_list type_env type_info args with
			TermListExactlyConverted(new_var_types,updated_type_info,converted_args)
		      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
			  let new_trm_ty = FormUtil.mk_fun_type [converted_ty] FormUtil.mk_bool_type in
			  let var_name = Util.fresh_name "v" in
			  let typed_var = FormUtil.mk_typedvar var_name converted_ty in
			  let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) converted_args) in
			  let new_trm = FormUtil.mk_typedform (Binder(Lambda,[(var_name,converted_ty)],comparison), new_trm_ty) in
			  TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		      | TermListApproximationNeeded -> TermApproximationNeeded
		      | NoTermListConversionNeeded ->
			  let _ = Util.warn ("get_rid_of_sets_in_trm: in the following input, the type was converted, but the terms were not, which is strange: "^(PrintForm.string_of_form trm)^".\n") in
			  let new_trm_ty = FormUtil.mk_fun_type [converted_ty] FormUtil.mk_bool_type in
			  let var_name = Util.fresh_name "v" in
			  let typed_var = FormUtil.mk_typedvar var_name converted_ty in
			  let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) args) in
			  let new_trm = FormUtil.mk_typedform (Binder(Lambda,[(var_name,converted_ty)],comparison), new_trm_ty) in
			  TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,new_trm))
		| NoTypeConversionNeeded -> 
		    (match get_rid_of_sets_in_trm_list type_env type_info args with
			TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
			  let new_trm_ty = FormUtil.mk_fun_type [ty] FormUtil.mk_bool_type in
			  let var_name = Util.fresh_name "v" in
			  let typed_var = FormUtil.mk_typedvar var_name ty in
			  let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) converted_args) in
			  let new_trm = FormUtil.mk_typedform (Binder(Lambda,[(var_name,ty)],comparison), new_trm_ty) in
			  TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		      | TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
			  let new_trm_ty = FormUtil.mk_fun_type [ty] FormUtil.mk_bool_type in
			  let var_name = Util.fresh_name "v" in
			  let typed_var = FormUtil.mk_typedvar var_name ty in
			  let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) converted_args) in
			  let new_trm = FormUtil.mk_typedform (Binder(Lambda,[(var_name,ty)],comparison), new_trm_ty) in
			  TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		      | TermListApproximationNeeded -> TermApproximationNeeded
		      | NoTermListConversionNeeded ->
			  let new_trm_ty = FormUtil.mk_fun_type [ty] FormUtil.mk_bool_type in
			  let var_name = Util.fresh_name "v" in
			  let typed_var = FormUtil.mk_typedvar var_name ty in
			  let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) args) in
			  let new_trm = FormUtil.mk_typedform (Binder(Lambda,[(var_name,ty)],comparison), new_trm_ty) in
			  TermExactlyConverted(MapOfVars.empty,type_info,new_trm))
	      )
	  | _ -> failwith ("get_rid_of_sets_in_trm: finite sets should have a set type, but they don't have it in the following input: "^(PrintForm.string_of_form trm)^".\n"))
    | App(Const FiniteSetConst,((arg::_) as args)) ->
        let type_env_as_list = mapVarType2typeEnv type_env in
	let ty = TypeReconstruct.get_type type_env_as_list arg in
	(match try_get_rid_of_sets_in_type ty with
	    TypeExactlyConverted converted_ty ->
	      (match get_rid_of_sets_in_trm_list type_env type_info args with
		  TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		    let var_name = Util.fresh_name "v" in
		    let typed_var = FormUtil.mk_typedvar var_name converted_ty in
		    let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) converted_args) in
		    let new_trm = Binder(Lambda,[(var_name,converted_ty)],comparison) in
		    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		| TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		    let var_name = Util.fresh_name "v" in
		    let typed_var = FormUtil.mk_typedvar var_name converted_ty in
		    let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) converted_args) in
		    let new_trm = Binder(Lambda,[(var_name,converted_ty)],comparison) in
		    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		| TermListApproximationNeeded -> TermApproximationNeeded
		| NoTermListConversionNeeded ->
		    let _ = Util.warn ("get_rid_of_sets_in_trm: in the following input, the type was converted, but the terms were not, which is strange: "^(PrintForm.string_of_form trm)^".\n") in
		    let var_name = Util.fresh_name "v" in
		    let typed_var = FormUtil.mk_typedvar var_name converted_ty in
		    let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) args) in
		    let new_trm = Binder(Lambda,[(var_name,converted_ty)],comparison) in
		    TermExactlyConverted(MapOfVars.empty,type_info,new_trm))
	  | NonObjSetTypesPresent converted_ty -> 
	      (match get_rid_of_sets_in_trm_list type_env type_info args with
		  TermListExactlyConverted(new_var_types,updated_type_info,converted_args)
		| TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		    let var_name = Util.fresh_name "v" in
		    let typed_var = FormUtil.mk_typedvar var_name converted_ty in
		    let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) converted_args) in
		    let new_trm = Binder(Lambda,[(var_name,converted_ty)],comparison) in
		    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		| TermListApproximationNeeded -> TermApproximationNeeded
		| NoTermListConversionNeeded ->
		    let _ = Util.warn ("get_rid_of_sets_in_trm: in the following input, the type was converted, but the terms were not, which is strange: "^(PrintForm.string_of_form trm)^".\n") in
                    let var_name = Util.fresh_name "v" in
		    let typed_var = FormUtil.mk_typedvar var_name converted_ty in
		    let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) args) in
		    let new_trm = Binder(Lambda,[(var_name,converted_ty)],comparison) in
		    TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,new_trm))
	  | NoTypeConversionNeeded -> 
	      (match get_rid_of_sets_in_trm_list type_env type_info args with
		  TermListExactlyConverted(new_var_types,updated_type_info,converted_args) ->
		    let var_name = Util.fresh_name "v" in
		    let typed_var = FormUtil.mk_typedvar var_name ty in
		    let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) converted_args) in
		    let new_trm = Binder(Lambda,[(var_name,ty)],comparison) in
		    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		| TermListNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_args) ->
		    let var_name = Util.fresh_name "v" in
		    let typed_var = FormUtil.mk_typedvar var_name ty in
		    let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) converted_args) in
		    let new_trm = Binder(Lambda,[(var_name,ty)],comparison) in
		    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		| TermListApproximationNeeded -> TermApproximationNeeded
		| NoTermListConversionNeeded ->
		    let var_name = Util.fresh_name "v" in
		    let typed_var = FormUtil.mk_typedvar var_name ty in
		    let comparison = FormUtil.mk_or (List.map (fun a -> FormUtil.mk_eq (typed_var,a)) args) in
		    let new_trm = Binder(Lambda,[(var_name,ty)],comparison) in
		    TermExactlyConverted(MapOfVars.empty,type_info,new_trm)))
    | Binder(b,til,f) ->
	let (inner_type_env,set_of_local_names,list_of_local_types) = List.fold_right
	  (fun (v,t) (sofar_env,sofar_local_names,sofar_tys) -> ((MapOfVars.add v t sofar_env),(SetOfVars.add v sofar_local_names),(t::sofar_tys)))
	  til (type_env,SetOfVars.empty,[]) in
	(match try_get_rid_of_sets_in_type_list list_of_local_types with
	    TypeListExactlyConverted tl ->
              (match get_rid_of_sets_in_trm inner_type_env type_info f with
		  TermExactlyConverted(new_var_types,updated_type_info,converted_f) ->
		    let new_til = List.fold_right2 (fun (v,_) new_t sofar -> (v,new_t)::sofar) til tl [] in
		    let remaining_changed = MapOfVars.fold
		      (fun v t sofar_remaining -> if SetOfVars.mem v set_of_local_names then sofar_remaining else MapOfVars.add v t sofar_remaining)
		      new_var_types MapOfVars.empty in
		    let new_trm = Binder(b,new_til,converted_f) in
		    TermExactlyConverted(remaining_changed,updated_type_info,new_trm)
		| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_f) ->
		    let new_til = List.fold_right2 (fun (v,_) new_t sofar -> (v,new_t)::sofar) til tl [] in
		    let remaining_changed = MapOfVars.fold
		      (fun v t sofar_remaining -> if SetOfVars.mem v set_of_local_names then sofar_remaining else MapOfVars.add v t sofar_remaining)
		      new_var_types MapOfVars.empty in
		    let new_trm = Binder(b,new_til,converted_f) in
		    TermNonObjSetsProbablyLeft(remaining_changed,updated_type_info,new_trm)
		| TermApproximationNeeded -> TermApproximationNeeded
		| NoTermConversionNeeded -> 
		    let _ = Util.warn ("get_rid_of_sets_in_trm: some bounded variables were converted, but the terms were not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		    let new_til = List.fold_right2 (fun (v,_) new_t sofar -> (v,new_t)::sofar) til tl [] in
		    let new_trm = Binder(b,new_til,f) in
		    TermExactlyConverted(MapOfVars.empty,type_info,new_trm))
	  | TypeListWithNonObjSet tl ->
              (match get_rid_of_sets_in_trm inner_type_env type_info f with
		  TermExactlyConverted(new_var_types,updated_type_info,converted_f)
		| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_f) ->
		    let new_til = List.fold_right2 (fun (v,_) new_t sofar -> (v,new_t)::sofar) til tl [] in
		    let remaining_changed = MapOfVars.fold
		      (fun v t sofar_remaining -> if SetOfVars.mem v set_of_local_names then sofar_remaining else MapOfVars.add v t sofar_remaining)
		      new_var_types MapOfVars.empty in
		    let new_trm = Binder(b,new_til,converted_f) in
		    TermNonObjSetsProbablyLeft(remaining_changed,updated_type_info,new_trm)
		| TermApproximationNeeded -> TermApproximationNeeded
		| NoTermConversionNeeded -> 
		    let _ = Util.warn ("get_rid_of_sets_in_trm: some bounded variables were converted, but the terms were not converted in the following input: "^(PrintForm.string_of_form trm)^".\n") in
		    let new_til = List.fold_right2 (fun (v,_) new_t sofar -> (v,new_t)::sofar) til tl [] in
		    let new_trm = Binder(b,new_til,f) in
		    TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,new_trm))
	  | NoTypeListConversionNeeded ->
              (match get_rid_of_sets_in_trm inner_type_env type_info f with
		  TermExactlyConverted(new_var_types,updated_type_info,converted_f) ->
		    let remaining_changed = MapOfVars.fold
		      (fun v t sofar_remaining -> if SetOfVars.mem v set_of_local_names then sofar_remaining else MapOfVars.add v t sofar_remaining)
		      new_var_types MapOfVars.empty in
		    let new_trm = Binder(b,til,converted_f) in
		    TermExactlyConverted(remaining_changed,updated_type_info,new_trm)
		| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_f) ->
		    let remaining_changed = MapOfVars.fold
		      (fun v t sofar_remaining -> if SetOfVars.mem v set_of_local_names then sofar_remaining else MapOfVars.add v t sofar_remaining)
		      new_var_types MapOfVars.empty in
		    let new_trm = Binder(b,til,converted_f) in
		    TermNonObjSetsProbablyLeft(remaining_changed,updated_type_info,new_trm)
		| TermApproximationNeeded -> TermApproximationNeeded
		| NoTermConversionNeeded -> NoTermConversionNeeded))
    | TypedForm(f,ty) -> 
        (match try_get_rid_of_sets_in_type ty with
	    TypeExactlyConverted new_ty ->
              (match get_rid_of_sets_in_trm type_env type_info f with
		  TermExactlyConverted(new_var_types,updated_type_info,converted_f) ->
		    let new_trm = overwritingly_attach_type converted_f new_ty in
		    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_f) ->
		    let new_trm = overwritingly_attach_type converted_f new_ty in
		    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		| TermApproximationNeeded -> TermApproximationNeeded
		| NoTermConversionNeeded ->
		    let new_trm = overwritingly_attach_type f new_ty in
		    TermExactlyConverted(MapOfVars.empty,type_info,new_trm))
	  | NonObjSetTypesPresent new_ty ->
              (match get_rid_of_sets_in_trm type_env type_info f with
		  TermExactlyConverted(new_var_types,updated_type_info,converted_f)
		| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_f) ->
		    let new_trm = overwritingly_attach_type converted_f new_ty in
		    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		| TermApproximationNeeded -> TermApproximationNeeded
		| NoTermConversionNeeded ->
		    let new_trm = overwritingly_attach_type f new_ty in
		    TermNonObjSetsProbablyLeft(MapOfVars.empty,type_info,new_trm))
	  | NoTypeConversionNeeded ->
              (match get_rid_of_sets_in_trm type_env type_info f with
		  TermExactlyConverted(new_var_types,updated_type_info,converted_f) ->
		    let new_trm = overwritingly_attach_type converted_f ty in
		    TermExactlyConverted(new_var_types,updated_type_info,new_trm)
		| TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,converted_f) ->
		    let new_trm = overwritingly_attach_type converted_f ty in
		    TermNonObjSetsProbablyLeft(new_var_types,updated_type_info,new_trm)
		| TermApproximationNeeded -> TermApproximationNeeded
		| NoTermConversionNeeded -> NoTermConversionNeeded))
    | _ -> failwith ("get_rid_of_sets_in_trm: cannot handle the following input: "^(PrintForm.string_of_form trm)^".\n")
and
(** [get_rid_of_sets_in_trm_list type_env type_info trm_list]
    recursively rewrites terms of the object set type in the list of terms trm_list, noticing whether other sets are present, and possibly cancelling the conversion. The constants representing functions accepting or returning object sets are replaced by fixed-named variables with a higher-order function type, the constants representing object sets are replaced by fixed-name predicates. The map type_env binds variables to their types. type_info contains information about what fixed-named functions and predicates are already needed, as well as what axioms are already needed. *)
  get_rid_of_sets_in_trm_list (type_env:mapVarType) (type_info:typeInformation) (trm_list:form list) : termListConvertResult =
  let (conversion_needed,nonobj_sets_encountered,approximation_needed,updated_type_env,updated_type_info,new_term_list) =
    List.fold_right
      (fun curr_term (sofar_conversion_needed,nonobj_sets_already_seen,approximation_already_needed,sofar_type_env,sofar_type_info,sofar_term_list) ->
	match get_rid_of_sets_in_trm type_env sofar_type_info curr_term with
	    TermExactlyConverted(update_to_type_env,new_type_info,new_term) ->
	      (true,nonobj_sets_already_seen,approximation_already_needed,(unionMapVarType_preferFirst update_to_type_env sofar_type_env),new_type_info,(new_term::sofar_term_list))
	  | TermNonObjSetsProbablyLeft(update_to_type_env,new_type_info,new_term) ->
	      (true,true,approximation_already_needed,(unionMapVarType_preferFirst update_to_type_env sofar_type_env),new_type_info,(new_term::sofar_term_list))
	  | TermApproximationNeeded -> (sofar_conversion_needed,nonobj_sets_already_seen,true,sofar_type_env,sofar_type_info,(curr_term::sofar_term_list))
	  | NoTermConversionNeeded -> (sofar_conversion_needed,nonobj_sets_already_seen,approximation_already_needed,sofar_type_env,type_info,(curr_term::sofar_term_list))
      )
      trm_list (false,false,false,MapOfVars.empty,type_info,[]) in
  if approximation_needed then TermListApproximationNeeded
  else
    if conversion_needed then
      if nonobj_sets_encountered then TermListNonObjSetsProbablyLeft(updated_type_env,updated_type_info,new_term_list)
      else TermListExactlyConverted(updated_type_env,updated_type_info,new_term_list)
    else NoTermListConversionNeeded

(** [change_var_types_in_a_term type_env type_info trm new_type_env]
    changes the type of the free variables of trm according to new_type_env. The current type environment of trm is type_env. type_info provides information on how operators on object sets should be named. 
    Does not change more term or variable types than needed.
    Returns either 
    - TermExactlyConverted(extra_type_env,updated_type_info,new_trm), if the term could be exactly converted, where 
      - extra_type_env contains information about what other variables had to change their type,
      - updated_type_info contains more information about the necessary operations on the predicate-on-objects type 
      - new_trm is the converted term,
    - TermNonObjSetsProbablyLeft(extra_type_env,updated_type_info,new_trm), if the term could not be exactly converted, but possibly still useful, where
      - extra_type_env contains information about what other variables had to change their type,
      - updated_type_info contains more information about the necessary operations on the predicate-on-objects type ,
      - new_trm is the converted term,
    - TermApproximationNeeded, if the term could not be converted at all and has to be approximated,
    - NoConversionNeeded, if the term does not need to be converted.
*)
(*
let change_var_types_in_a_term (type_env:mapVarType) (type_info:typeInformation) (trm:form) (new_type_env:mapVarType) : termConversionResult =
  match trm with
      Var v ->
        (try
	   let ty = MapOfVars.find v new_type_env in
	   let new_trm = FormUtil.mk_typedform (trm,ty) in
	   TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
	 with Not_found -> NoConversionNeeded)
    | TypedForm(((Var v) as var),ty) ->
        (try
	   let ty = MapOfVars.find v new_type_env in
	   let new_trm = FormUtil.mk_typedform (var,ty) in
	   TermExactlyConverted(MapOfVars.empty,type_info,new_trm)
	 with Not_found -> NoConversionNeeded)
    | Const _ -> NoConversionNeeded
    | App(f,fs) -> TODO
*)


(** [translate_sequent_to_AUFLIA options env sq]
    approximates sq by a sequent that fully lies in the AUFLIA fragment. The types of the free variables are given in env. 
    The approximation preserves validity. 
    Returns (new_env, new_asms,new_succ) where (new_asms,new_succ) is the resulting sequent and new_env is its type environment. *)
(* 
let translate_sequent_to_AUFLIA (options:options_t) (env0 : mapVarType) (s0 : sequent) : (mapVarType * form list * form) =
  (* Remove unnecessary variables. *)
  let (env1,s1) = ElimFvForAUFLIA.elim_fv_in_seq_for_AUFLIA true env0 s0 in
  (* In needed, abstract reflexive-transitive closure away. *)
  let (env2,s2) = 
    if flag_positive options "KeepRtrancl" 
    then (env1,s1)
    else
      let pseudos_with_types_and_consumed_numbers = List.map (fun (s,t)-> (s,t,1)) pseudo_constants in
      let (env_temp,s_temp) = smart_abstract_constructs_in_sequent pseudos_with_types_and_consumed_numbers env1 s1 in
      ElimFvForAUFLIA.elim_fv_in_seq_for_AUFLIA false env_temp s_temp in
  (* Avoid name conflicts. *)
  let (env3,s3) = sanitize_sequent_wrt_keywords_for_SMTLIB2 env2 s2 in
  (* If needed, abstract information about filed ranges, cardinalities away. *)
  let s4 =
    if flag_positive options "KeepPointstos" 
    then s3
    else 
      let f_temp = smart_abstract_constructs [(mk_var points_to_name, 3)] (form_of_sequent s3) in
      let f_temp,_ = TypeReconstruct.reconstruct_types [] f_temp in
      let s_temp = sequent_of_form (attach_type_if_not_attached f_temp (TypeApp(TypeBool,[]))) in
      elim_fv_in_seq false s_temp in
  (* Abstract constant cardinalities away. *)
  let f5 = fst (TypeReconstruct.reconstruct_types [] (smart_abstract_constructs [(Cardeq,1),(Cardleq,1),(Cardgeq,1)] (form_of_sequent s4))) in
  (* Resolve ambiguous operators and remove lambda abstraction *)
  let f6 = disambiguate (unlambda ~keep_comprehensions:false f) in
  TODO
  TODO
 *)
