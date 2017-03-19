(** Formula manipulation procedures that that work on variables sets stored as trees instead of sets stored as lists. *)

open Form

(* Faster managing of sets of free variables as trees *)
module MapOfVars = Map.Make(String)
type mapVarForm = form MapOfVars.t
module SetOfVars = Set.Make(String)
type setOfVars = SetOfVars.t

(** [fv_set f] computes the set of free variables of the formula f. *)
let fv_set: form -> setOfVars =
  (* [fv1 bv acc_fv f] computes 
     the union of acc_fv with the set of those of free variables of the formula f that are not in bv. *)
  let rec fv1 (bv:setOfVars) (acc_fv:setOfVars) (f:form) : setOfVars =
    match f with
	App(f1,fs) -> fv1 bv (List.fold_left (fv1 bv) acc_fv fs) f1
      | Binder(_,tvs,f1) -> fv1 (List.fold_left (fun sofar (x,_) -> SetOfVars.add x sofar) bv tvs) acc_fv f1
      | Var v -> if SetOfVars.mem v bv then acc_fv else SetOfVars.add v acc_fv
      | Const _ -> acc_fv
      | TypedForm(f1,_) -> fv1 bv acc_fv f1
  in fv1 SetOfVars.empty SetOfVars.empty

(** [fv_set_of_formlist fs] computes the set of free variables of the list of formulas fs. *)
(* currently unused *)
let fv_set_of_formlist : ((form list) -> setOfVars) =
  (* [fv1 bv acc_fv f] computes 
     the union of acc_fv with the set of those of free variables of the formula f that are not in bv. *)
  let rec fv1 (bv:setOfVars) (acc_fv:setOfVars) : form -> setOfVars = function
	App(f1,args) -> fv1 bv (fv_many bv acc_fv args) f1
      | Binder(_,tvs,f1) -> fv1 (List.fold_left (fun sofar (x,_) -> SetOfVars.add x sofar) bv tvs) acc_fv f1
      | Var v -> if SetOfVars.mem v bv then acc_fv else SetOfVars.add v acc_fv
      | Const _ -> acc_fv
      | TypedForm(f1,_) -> fv1 bv acc_fv f1
  and
  (* [fv_many bv acc_fv fs] computes 
     the union of acc_fv with the set of those of free variables of the formulas in fs that are not in bv. *)
    fv_many (bv:setOfVars) (acc_fv:setOfVars) : form list -> setOfVars = 
      let fv1_bv = fv1 bv in List.fold_left fv1_bv acc_fv
  in fv_many SetOfVars.empty SetOfVars.empty

(** [isfree_var x f] returns
    - true, if x freely occurs in the formula f at least once
    - false, if x occurs only boundedly or does not occur at all in f. *)
let isfree_var (x:ident) : form->bool = 
  let rec isfreevarx = function
    App (f1,fs) -> (isfreevarx f1) || (List.exists isfreevarx fs)
  | Binder(_,tvs,f1) -> (isfreevarx f1) && not (List.mem_assoc x tvs)
  | Var v -> v=x
  | Const _ -> false
  | TypedForm(f1,_) -> isfreevarx f1
  in isfreevarx

(** [isfree_var_in_formlist x fs]
    determines whether a variable x occurs freely in any of the formulas from fs. *)
let isfree_var_in_formlist (x:ident) : ((form list) -> bool)  =
  let rec isfreevarx = function
      App (f1,fs) -> (isfreevarx f1) || (List.exists isfreevarx fs)
    | Binder(_,tvs,f1) -> (isfreevarx f1) && not (List.mem_assoc x tvs)
    | Var v -> v=x
    | Const _ -> false
    | TypedForm(f1,_) -> isfreevarx f1
  in List.exists isfreevarx

type mapVarType = typeForm MapOfVars.t

(** [typed_fv_set_of_formlist fs te]
    computes the set of free variables of the formulas in fs in the type environment te, returning a map from variable names to types. 
    If a variable is typed differently in different formulas, only one of the types is kept. *)
let typed_fv_set_of_formlist (flst:(form list)) (te: mapVarType) : mapVarType =
  (* [fv1 bv acc_fv ff] computes 
     the union of acc_fv with the set of those of free variables 
     of the formulas in ff that are not in bv. *)
  let rec fv1 (bv:setOfVars) (acc_fv:mapVarType) (ff:form list) : mapVarType =
    match ff with
	[] -> acc_fv
      | g::gs ->
	(match g with
	    App(f1,fs) -> fv1 bv (fv1 bv acc_fv (f1::fs)) gs
	  | Binder(_,tvs,f1) -> fv1 bv (fv1 (List.fold_left (fun sofar (x,_) -> SetOfVars.add x sofar) bv tvs) acc_fv [f1]) gs
	  | TypedForm(Var v, tf) -> fv1 bv (if SetOfVars.mem v bv then acc_fv else MapOfVars.add v tf acc_fv) gs
	  | Const _ -> fv1 bv acc_fv gs
	  | TypedForm(f1,_) -> fv1 bv acc_fv (f1::gs)
	  | Var x ->
	      if SetOfVars.mem x bv then fv1 bv acc_fv gs
	      else 
		try let new_acc_fv = MapOfVars.add x (MapOfVars.find x te) acc_fv in fv1 bv new_acc_fv gs
		with Not_found -> failwith ("All free variables should be typed, but in the formula list ["^(String.concat " ; " (List.map PrintForm.string_of_form flst))^"]the variable "^x^" is not typed.\n"))
  in fv1 SetOfVars.empty MapOfVars.empty flst

(** [is_type_a_set_of x y]
    checks whether x is equivalent to the type set-of-y. *)
let is_type_a_set_of (x:typeForm) (y:typeForm) =
  (match x with
      TypeApp(TypeSet,[z]) -> FormUtil.equal_types z y
    | _ -> false)

(** [is_objset_type ty]
    checks whether ty is the type of set-of-objects. *)
let is_objset_type (ty:typeForm) : bool = 
  (FormUtil.normalize_type ty) = (TypeApp(TypeSet,[TypeApp(TypeObject,[])]))

(** [typeEnv2mapVarType te]
    converts a list representation of an environment into a map representation. *)
let typeEnv2mapVarType : typeEnv -> mapVarType = 
  List.fold_left (fun sofar (v,ty) -> MapOfVars.add v ty sofar) MapOfVars.empty 

(** [mapVarType2typeEnv mvt]
    converts a map representation of an environment into a list representation. *)
let mapVarType2typeEnv : mapVarType -> typeEnv = MapOfVars.bindings

(** [string_of_mapVarType mvt]
    converts an environment into a printable form. *)
let string_of_mapVarType (mvt:mapVarType) : string =
  try
    let (v,ty) = MapOfVars.min_binding mvt in
    let v_and_ty_as_string = (v^" :: "^(PrintForm.string_of_type ty)) in
    let remainder = MapOfVars.remove v mvt in
    MapOfVars.fold (fun x x_ty sofar -> (sofar^",  "^x^" :: "^(PrintForm.string_of_type x_ty))) remainder v_and_ty_as_string
  with Not_found -> "[]"

(** [is_finite_type ty]
    returns true if the universe of the type ty is always finite. *)
let rec is_finite_type = function
    TypeUniverse | TypeVar _ -> false
  | TypeApp (st,tfl) -> 
    (match st with
	TypeUnit | TypeBool | TypeObject -> true (* The set of objects is finite! *)
      | TypeInt | TypeString | TypeDefined _ -> false
      | TypeSet | TypeList | TypeArray -> is_finite_type_list tfl)
  | TypeFun(tfl,tl) -> (is_finite_type_list tfl) && (is_finite_type tl)
  | TypeProd(tfl) -> is_finite_type_list tfl
and
(** [is_finite_type_list tl]
    returns true if the universe of all the types of tl is always finite. *)
    is_finite_type_list tl = List.for_all is_finite_type tl

(** [attach_type_if_not_attached f ty]
    returns a formula f, typed by ty, if f was untyped before,
    returns f, otherwise. *)
let attach_type_if_not_attached (f:form) (ty:typeForm) :form = 
  match f with
      TypedForm (_,_) -> f
    | _ -> TypedForm(f,ty)

(** [overwritingly_attach_type f ty]
    returns a formula f, typed by ty. If the formula was previously typed, the old type is forgotten. *)
let overwritingly_attach_type (f:form) (ty:typeForm) :form = 
  match f with
      TypedForm(g,_) -> TypedForm(g,ty)
    | _ -> TypedForm(f,ty)

(* A more efficient substitution where sets of variables are stored as trees. *)
(** [nsubst m f]
    where m={(id_1,g_1),...,(id_n,g_n)} is a (naive) substitution
    syntactically replaces all free occurences of id_i in f with g_i (i<=n). 
    No renaming takes place. The replacement does not look into g_i (i<=n).
    Be careful: to make sure that the resulting formula is equivalent to f[g_1/id_1,...,g_n/id_n],
    make sure that g_i are fresh variables or contain only such variables that are not bound in f.
*)
let rec nsubst (m:mapVarForm) (f:form) : form =
  match f with
      App(f1,fs) -> App(nsubst m f1, List.map (nsubst m) fs)
    | Binder(bnd,tvs,f1) ->
        let m1 = MapOfVars.filter (fun id _ -> not (List.mem_assoc id tvs)) m in
        if MapOfVars.is_empty m1 then f else Binder(bnd,tvs,(nsubst m1 f1))
    | Var v -> (try MapOfVars.find v m with Not_found -> f)
    | Const _ -> f
    | TypedForm(f1,t) -> TypedForm((nsubst m f1),t)

(** [capture_avoid avoid_vars tvs]
    computes (tvs1,renaming) where 
    tvs1 is a new list of bound variables that is disjoint from avoid_vars and coincides at as many places with tvs 
    as possible, and renaming is a substitution of variables from tvs by variables from tvs1. *)
let capture_avoid (avoid_vars:setOfVars) : ((typedIdent list) -> ((typedIdent list) * mapVarForm)) = 
  (* [capture_avoid_aux til sbst tvs]
     computes (((rev til)@tvs1),(renaming union sbst)) where tvs1 is a new list of bound variables that is disjoint 
     from avoid_vars and coincides at as many places with tvs as possible,
     and renaming is a substitution of variables from tvs by variables from tvs1. *)
  let rec capture_avoid_aux (tvs_acc: typedIdent list) (subst_acc:mapVarForm) = function
      [] -> ((List.rev tvs_acc),subst_acc)
    | (v,t)::tvs1 -> 
        if (SetOfVars.mem v avoid_vars) then
          let fresh_v = Util.fresh_name v in
          capture_avoid_aux ((fresh_v,t)::tvs_acc) (MapOfVars.add v (Var fresh_v) subst_acc) tvs1 
        else
          capture_avoid_aux ((v,t)::tvs_acc) subst_acc tvs1
  in capture_avoid_aux [] MapOfVars.empty

(** [fv_of_subst m]
    returns the free variables of the range of the substitution m. *)
let fv_set_of_subst (m:mapVarForm) : setOfVars =
  MapOfVars.fold (fun v f sofar -> SetOfVars.union sofar (fv_set f)) m (SetOfVars.empty)

(** [compareConstValue c1 c2]
    compares two constants. Returns 0 if constants are equal and in certain simple equivalence cases, -1 or +1 if constants are different. 
    Strings, booleans, integers are compared by their usual order. *)
let compareConstValue: constValue -> constValue -> int =
  let intOfConst = function (* take just any total order*)
      Eq | MetaEq -> 0
    | Elem -> 1
    | Or -> 2
    | And |MetaAnd -> 3
    | Not -> 4
    | Impl|MetaImpl ->5
    | Iff -> 6
    | Disjoint -> 7
    | Lt -> 8
    | Gt -> 9
    | LtEq -> 10
    | GtEq -> 11
    | Card -> 12
    | Cardeq -> 13
    | Cardleq -> 14
    | Cardgeq -> 15
    | ArrayRead -> 16
    | ArrayWrite -> 17
    | FieldWrite -> 18
    | FieldRead -> 19
    | Cap -> 20
    | Cup -> 21
    | Diff -> 22
    | Subseteq -> 23
    | Subset -> 24
    | Seteq -> 25
    | UMinus -> 26
    | Plus -> 27
    | Minus -> 28
    | Mult -> 29
    | Div -> 30
    | Mod -> 31
    | IntConst _ -> 32
    | BoolConst _ -> 33
    | NullConst -> 34
    | StringConst _ -> 35
    | EmptysetConst -> 36
    | FiniteSetConst -> 37
    | UniversalSetConst -> 38
    | Tuple -> 39
    | ListLiteral -> 40
    | Let -> 41
    | Rtrancl -> 42
    | Rimage -> 43
    | Unit -> 44
    | Comment -> 45
    | Old -> 46
    | ObjLocs -> 47
    | Ite ->48
  in fun (c1:constValue) (c2:constValue) ->
    match (c1,c2) with
        ((IntConst x),(IntConst y)) -> compare x y
      | ((BoolConst x),(BoolConst y)) -> compare x y
      | ((StringConst x),(StringConst y)) -> String.compare x y
      | (x,y) when x=y -> 0
      | _ -> compare (intOfConst c1) (intOfConst c2)

(** [isOpOverMultiset c]
    determines whether a function symbol c is commutative and associative. *)
let isOpOverMultiset = function
  Or | And | MetaAnd | Disjoint | Cap | Cup -> true
  | _ -> false

(** [compareSimpleTypes t1 t2]
    compares two simple types. Returns 0 if the types are equal and in certain simple equivalence cases, -1 or +1 if they are different. *)
let rec compareSimpleTypes : simpleType -> simpleType -> int =
  let intOfSimpleType = function
      TypeUnit -> 0
    | TypeInt -> 1
    | TypeString -> 2
    | TypeBool -> 3
    | TypeObject -> 4
    | TypeSet -> 5
    | TypeList -> 6
    | TypeArray -> 7
    | TypeDefined _ -> 8
  in fun (st1:simpleType) (st2:simpleType) ->
    match (st1,st2) with 
	((TypeDefined x), (TypeDefined y)) -> String.compare x y
      | (x,y) when x=y -> 0
      | _ -> Pervasives.compare (intOfSimpleType st1) (intOfSimpleType st2)

(** [compareType t1 t2]
    compares two types t1 and t2. Returns 0 if the types are equal and in certain simple equivalence cases, -1 or +1 if they are different. *)
let rec compareType (t1:typeForm) (t2:typeForm) : int =
  (match ((FormUtil.normalize_type t1),(FormUtil.normalize_type t2)) with
      (TypeUniverse,TypeUniverse) -> 0
    | (TypeUniverse,_) -> -1
    | ((TypeVar _),TypeUniverse) -> 1
    | ((TypeVar x1),(TypeVar x2)) -> String.compare x1 x2
    | ((TypeVar _),_) -> -1
    | ((TypeApp (_,_)),TypeUniverse) | ((TypeApp (_,_)),(TypeVar _)) -> 1
    | ((TypeApp (t1,tl1)),(TypeApp (t2,tl2))) -> 
      let c=compareSimpleTypes t1 t2 in
      if c=0 then compareTypeList tl1 tl2 else c
    | ((TypeApp (_,_)),_) -> -1
    | ((TypeFun (_,_)),(TypeProd _)) -> -1
    | ((TypeFun (tl1,tf1)),(TypeFun (tl2,tf2))) ->
      let c=compareTypeList tl1 tl2 in
      if c=0 then compareType tf1 tf2 else c
    | ((TypeFun (_,_)),_) -> 1
    | ((TypeProd tl1),(TypeProd tl2)) -> compareTypeList tl1 tl2
    | ((TypeProd _),_) -> 1)
and (* Compare two lists of types: *)
    compareTypeList (tl1: typeForm list) (tl2: typeForm list) : int =
  (match (tl1,tl2) with
      ([],[]) -> 0
    | (_,[]) -> 1
    | ([],_) -> -1
    | ((x::xs),(y::ys)) -> 
      let v= (compareType x y) in
      if v=0 then compareTypeList xs ys else v)

(** [compareForm f1 f2]
    defines a total order on the formulas. Returns 0 if input formulas are equal and in certain simple equivalent cases, -1 or +1 if they are different. 
    Differences in associative-and-commutative operations are ignored, as well as in alpha-renaming of bounded variables. *)
let compareForm =
  (* The actual comparison function: *)
  let rec compareFormAux (f1:form) (f2:form) =
    match (f1,f2) with
        ((App((Const Comment),gl1)),_) -> compareFormLists gl1 [f2]
      | (_,(App((Const Comment),gl2))) -> compareFormLists [f1] gl2
      | (App (Const UMinus, [Const (IntConst i1)]), (Const (IntConst i2))) | (Const (IntConst i2), App (Const UMinus, [Const (IntConst i1)])) -> Pervasives.compare (-1 * i1)  i2
      | (App (Const FieldRead, [f; x]), _) -> compareFormAux (App (f, [x])) f2
      | (_, App (Const FieldRead, [f; x])) -> compareFormAux f1 (App (f, [x]))
      | (App (Const And, [g]), _) | (App (Const Or, [g]), _) -> compareFormAux g f2
      | (_,App (Const And, [g])) | (_,App (Const Or, [g])) -> compareFormAux f1 g
      | ((Var x),(Var y)) -> String.compare x y
      | ((Var _),_) -> -1
      | ((Const _),(Var _)) -> 1
      | ((Const x),(Const y)) -> compareConstValue x y
      | ((Const _),_) -> -1
      | ((App (_,_)),(Var _)) | ((App (_,_)),(Const _)) -> 1
      | ((App ((Const g1),gl1)),(App((Const g2),gl2))) -> 
	  let c = compareConstValue g1 g2 in 
	  if c=0 then
	    if isOpOverMultiset g1 then compareFormListsAsMultisets gl1 gl2
	    else compareFormLists gl1 gl2
	  else c
      | ((App (g1,gl1)),(App (g2,gl2))) -> compareFormLists (g1::gl1) (g2::gl2)
      | ((App (_,_)),_) -> 1
      | ((Binder(_,_,_)),(TypedForm (_,_))) -> -1
      | ((Binder(b1,til1,f1)),(Binder(b2,til2,f2))) -> 
          let c= compareBinders b1 b2 in
          if c=0 then compareBoundForm (til1,f1) (til2,f2) else c
      | ((Binder(_,_,_)),_) -> 1
      | ((TypedForm(f1,tf1)),(TypedForm(f2,tf2))) -> 
	  let c=compareFormAux f1 f2 in if c=0 then compareType tf1 tf2 else c
      | ((TypedForm(f1,tf1)),_) -> 1
  and (* compare two binders *)
      compareBinders (b1:binderKind) (b2:binderKind) :int =
    match (b1,b2) with
	(Lambda,Lambda) -> 0
      | (Lambda,_) -> -1
      | (Forall,Lambda) -> 1
      | (Forall,Forall) -> 0
      | (Forall,_) -> -1
      | (Exists,Comprehension) -> -1
      | (Exists,Exists) -> 0
      | (Exists,_) -> 1
      | (Comprehension,Comprehension) -> 0
      | (Comprehension,_) -> 1
  and (* Compare two formulas in environments of bound variables: *)
      compareBoundForm (til1,f1) (til2,f2) = 
    let c=compare (List.length til1) (List.length til2) in
    if c=0 then
      let (types_cmp,renaming1,renaming2) =
	List.fold_left2 
	  (fun ((sofar_types_cmp,sofar_renaming1,sofar_renaming2) as sofar) (x,xt) (y,yt) -> 
	    if sofar_types_cmp=0 then
	      let ct = compareType xt yt in
	      if ct=0 then
		if x=y then sofar
		else
		  let fresh_var = FormUtil.mk_var (Util.fresh_name x) in
		  (0,(MapOfVars.add x fresh_var sofar_renaming1),(MapOfVars.add y fresh_var sofar_renaming2))
	      else (ct,sofar_renaming1,sofar_renaming2)
	    else sofar
	  )
	  (0, MapOfVars.empty, MapOfVars.empty) til1 til2 in
      if types_cmp=0 then
	let g1 = nsubst renaming1 f1 in
	let g2 = nsubst renaming2 f2 in
	compareFormAux g1 g2
      else types_cmp
    else c
  and (* Compare two lists of formulas: *)
      compareFormLists gl1 gl2 = 
    match (gl1,gl2) with
	([],[]) -> 0
      | (_,[]) -> 1
      | ([],_) -> -1
      | ((x::xs),(y::ys)) -> 
	let v= (compareFormAux x y) in
	if v=0 then compareFormLists xs ys else v
  and (* Compare the multisets representation of two lists of formulas: *)
      compareFormListsAsMultisets gl1 gl2 =
    let h1 = List.sort compareFormAux gl1 in
    let h2 = List.sort compareFormAux gl2 in
    compareFormLists h1 h2
  in compareFormAux

(** [OrderedForm] is the structure for ordered formulas. *)
module OrderedForm = struct
  type t = form
  let compare = compareForm   (* Comparison up to the order in commutative operators, up to alpha-renaming, and up to the comments. *)
  (* Pervasives.compare would be an alternative. *) 
end

(** [MapOfForms] is the module for maps with the domain of formulas. *)
module MapOfForms = Map.Make(OrderedForm)
(** [mapFormVar] is the type of maps from formulas to typed identifiers. *)
type mapFormVar = typedIdent MapOfForms.t
(** [mapFormForm] is the type of maps from formulas to formulas. *)
type mapFormForm = form MapOfForms.t
(** [SetOfForms] is the module for sets of formulas. *)
module SetOfForms = Set.Make(OrderedForm)
(** [setOfForms] is the type for sets of formulas. *)
type setOfForms = SetOfForms.t

(** [preorder_typed_fv_list_of_form te f]
    returns the list of free variables in the order in which they occur in the formula f, together with their types. Multiple occurences of the same variable are listed several times. *)
(* not needed now *)
(*
let preorder_typed_fv_list_of_form (te:mapVarType) (f:form) : typedIdent list = 
  (* [postorder_typed_fv_of_list bv acc fs] computes 
      (the list of the free variables of the list fs in the postorder traversal)@acc. *)
  let rec postorder_typed_fv_of_list bv acc = function
      [] -> acc
    | g::fs -> 
      (match g with
        TypedForm(Var v,tf) -> postorder_typed_fv_of_list bv (if SetOfVars.mem v bv then acc else ((v,tf)::acc)) fs
      | TypedForm(f1,t) -> postorder_typed_fv_of_list bv acc (f1::fs)
      | App(f1,args) -> postorder_typed_fv_of_list bv acc (f1::args)
      | Binder(_,tvs,f1) -> 
	  let postorder_typed_fv_of_f = postorder_typed_fv_of_list (List.fold_right (fun (x,_) sofar -> SetOfVars.add x sofar) tvs bv) acc [f1] in
          postorder_typed_fv_of_list bv postorder_typed_fv_of_f fs
      | Const _ -> postorder_typed_fv_of_list bv acc fs
      | Var v -> 
          if SetOfVars.mem v bv then postorder_typed_fv_of_list bv acc fs
          else
	    try let new_acc = (v,(MapOfVars.find v te))::acc in postorder_typed_fv_of_list bv new_acc fs
	    with Not_found -> failwith ("All free variables should be typed, but in the formula "^(PrintForm.string_of_form f)^" the variable "^v^" is not typed.\n"))
  in List.rev (postorder_typed_fv_of_list SetOfVars.empty [] [f])
*)

(** [preorder_typed_fv_list_of_formlist te fs]
    returns the list of free variables in the order in which they occur in the formula list fs, together with their types. Multiple occurences of the same variable are listed several times. *)
(* not needed now *)
(*
let preorder_typed_fv_list_of_formlist (te : mapVarType) (fs : form list) : typedIdent list = 
  (* [postorder_typed_fv_of_list bv acc fs] computes 
      (the list of the free variables of the list fs in the postorder traversal)@acc. *)
  let rec postorder_typed_fv_of_list bv acc = function
      [] -> acc
    | g::gs -> 
      (match g with
        TypedForm(Var v,tf) -> postorder_typed_fv_of_list bv (if SetOfVars.mem v bv then acc else ((v,tf)::acc)) gs
      | TypedForm(f1,t) -> postorder_typed_fv_of_list bv acc (f1::gs)
      | App(f1,args) -> postorder_typed_fv_of_list bv acc (f1::args)
      | Binder(_,tvs,f1) -> 
	  let postorder_typed_fv_of_f = postorder_typed_fv_of_list (List.fold_right (fun (x,_) sofar -> SetOfVars.add x sofar) tvs bv) acc [f1] in
          postorder_typed_fv_of_list bv postorder_typed_fv_of_f gs
      | Const _ -> postorder_typed_fv_of_list bv acc gs
      | Var v -> 
          if SetOfVars.mem v bv then postorder_typed_fv_of_list bv acc gs
          else
	    try let new_acc = (v,(MapOfVars.find v te))::acc in postorder_typed_fv_of_list bv new_acc gs
	    with Not_found -> failwith ("All free variables should be typed, but in the formula list ["^String.concat ";" (List.map PrintForm.string_of_form fs)^"] the variable "^v^" is not typed.\n"))
  in List.rev (postorder_typed_fv_of_list SetOfVars.empty [] fs)
*)

(** [interMapVarType mvt1 mvt2]
    returns the intersection of type maps mvt1 and mvt2. Raises Invalid_argument, if on some of the values the types do not agree. *)
let interMapVarType : mapVarType -> mapVarType -> mapVarType =
  let check_types (key:ident) : (typeForm option) -> (typeForm option) -> (typeForm option)  = function 
        None -> (fun _ -> None)
      | Some ty1 -> (function
            None -> None
          | Some ty2 ->
	      if FormUtil.equal_types ty1 ty2 then Some ty1
	      else raise (Invalid_argument ("interMapVarType started on type environments in which the same variable "^key^" has two different types "^(PrintForm.string_of_type ty1)^" and "^(PrintForm.string_of_type ty2)^".\n")))
  in MapOfVars.merge check_types 

(** [unionMapVarType_preferFirst mvt1 mvt2]
    computes the union of two maps of type variables. In case a variable has a different type in the first and in the second map, take the first. *)
let unionMapVarType_preferFirst =
  let check_types (key:ident) : (typeForm option) -> (typeForm option) -> (typeForm option) = function 
      None -> (fun x -> x)
    | sty1 -> (fun _ -> sty1)
  in MapOfVars.merge check_types

(** [smart_abstract_construct_in_sequent [(s_1,ty_1,n_1);...;(s_k,ty_k,n_k)] env s]
    replaces in the sequent s the terms (s_1 a_{1,1} ... a_{1,n_1}), ... , (s_k a_{k,1} ... a_{k,n_k}), where all s_i are unbounded variables or constants (i<=n), by fresh symbols.
    Equal terms are replaced by equal symbols. The type environment of s is given by env. The type of each s_i is ty_i (1<=i<=n).
    If some s_i is not a bounded variable, boundedness is not checked - replacement happens anyway.
    Returns (the new type environment, the generated sequent).
*)
let smart_abstract_constructs_in_sequent (constrs : (form * typeForm * int) list) (env:mapVarType) ((antecedent,succedent) : sequent) : mapVarType*sequent =
  (** [consume i acc ts tys]
      splits the list of arguments ts, together with a list of their types tys, into the list of the first i elements of ts, followed by the rest and the types of the rest.
      Returns (((reverse acc)@(the first i elements of ts)), remaining elements of ts, types of the remaining elements). *)
  let rec consume i acc ts tys =
    if i = 0 then (List.rev acc, ts, tys) else
    match ts with
    | t::ts -> consume (i - 1) (t::acc) ts (List.tl tys)
    | _ -> (List.rev acc, ts, tys)
  in
  (* [freshen_var_name_with_respect_to_constrs var_name]
     generates a new variable name that is different from all the variable names in constrs. Returns
     - Some new_var_name if a fresh variable name was needed and was generated, and
     - None, otherwise. *)
  let rec freshen_var_name_with_respect_to_constrs (var_name:ident) : ident option =
    if List.exists 
         (fun (g,_,_) -> match g with
             Var name | TypedForm(Var name,_) -> name=var_name
           | Const x | TypedForm(Const x,_) -> (string_of_const x)=var_name
           | _ -> false )
         constrs
    then
      let fresh = Util.fresh_name var_name in
      match freshen_var_name_with_respect_to_constrs fresh with
          None -> Some fresh
        | very_fresh -> very_fresh
    else None
  in
  (* [replace replace_map global_env bounded_vars f fs]
     replaces the term (f fs) by (new_f id_list) where new_f is a fresh symbol and id_list is composed of those free variables of fs that are in the set bounded_vars.
     If (f fs) is present in replace_map, the value from there is used, otherwise a new term is created.
     The tuple (updated replace map, updated global environment, new term) is returned.
  *)
  let replace (replace_map:mapFormForm) (global_env: mapVarType) (bounded_vars : mapVarType) (f : form) (fs : form list) : (mapFormForm*mapVarType*form) =
    let key = App(f,fs) in
    try (replace_map, global_env, (MapOfForms.find key replace_map))
    with Not_found ->
      let totalEnvMap = unionMapVarType_preferFirst bounded_vars global_env in
      let fvs = typed_fv_set_of_formlist fs totalEnvMap in
      let ids = interMapVarType fvs bounded_vars in
      let args = MapOfVars.fold (fun var_name var_type sofar_list -> (FormUtil.mk_typedform(Var var_name,var_type))::sofar_list) ids [] in
      let stem_of_new_name = match f with 
          Var name | TypedForm(Var name,_) -> name
        | Const x | TypedForm(Const x,_) -> string_of_const x
        | _ -> "v" in
      let new_var_name = (match freshen_var_name_with_respect_to_constrs (stem_of_new_name^"_") with Some x -> x | None -> (Util.fresh_name stem_of_new_name)) in
      let new_var = FormUtil.mk_var new_var_name in
      let tyEnv = MapOfVars.bindings totalEnvMap in
      let type_of_key = TypeReconstruct.get_type tyEnv key in
      let f' = if args=[] then new_var else App(new_var,args) in
      let (f'',_) = TypeReconstruct.reconstruct_types tyEnv (FormUtil.mk_typedform(f',type_of_key)) in
      let new_replace_map = MapOfForms.add key f'' replace_map in
      let new_var_type = match f'' with
          TypedForm(Var v, ty) when v=new_var_name -> ty
        | TypedForm(App((TypedForm(Var v,ty)),_),_) when v=new_var_name -> ty
        | App((TypedForm(Var v,ty)),_) when v=new_var_name -> ty
        | _ -> failwith ("smart_abstract_constructs_in_sequent, subfunction replace, failed to find a type for a fresh symbol while replacing "^(PrintForm.string_of_form key)^".\n") in
      let new_global_env = MapOfVars.add new_var_name new_var_type global_env in
      (new_replace_map, new_global_env,f'')
    in
  (* [sanitize_single_var var_name bounded_form curr_constrs] 
     freshens variables in bounded_form whose name matches var_name if var_name is a variable in constrs. In this case returns
     (new_var_name,new_bounded_form,new_constrs) where new_var_name is the fresh variable name that is a replacement for var_name, new_bounded_form is the updated created formula and new_constrs is curr_constrs, 
     with the questionable construct removed.
     If var_name is not a variable in constrs, returns the arguments in a triple. *)
  let sanitize_single_var (var_name:ident) (bounded_form:form) (curr_constrs: (form * typeForm * int) list) : (ident*form*((form*typeForm*int) list)) = 
    match freshen_var_name_with_respect_to_constrs var_name with
        Some fresh_var_name -> 
          let new_bounded_form = nsubst (MapOfVars.add var_name (Var fresh_var_name) MapOfVars.empty) bounded_form in
          let new_constrs = List.filter (fun (g,_,_) -> match g with Var v | TypedForm(Var v,_) -> v<>var_name | _ -> true) curr_constrs in
          (fresh_var_name,new_bounded_form,new_constrs)
      | None -> (var_name,bounded_form,curr_constrs)
  in
  (* [abst_form replace_map global_env bounded_vars constrs f]
     abstracts the formula f by replacing the occurences of symbols in constrs with fresh symbols, taking bounded variables into account. The replacements are stored in replace_map, so equal replacements are named equally. The types of free variables are given in global_env, the types of bounded variables are given in bounded_vars. The tuple (updated replace map, updated global type environment, new formula) is returned. *)
  let rec abst_form (replace_map:mapFormForm) (global_env:mapVarType) (bounded_vars: mapVarType) (constrs: (form * typeForm * int) list) (f:form) : (mapFormForm*mapVarType*form) =
    match f with 
        Const _ | Var _ -> 
          if List.exists (fun (f',_,_) -> f'=f) constrs
          then replace replace_map global_env bounded_vars f []
          else (replace_map, global_env, f)
      | App(TypedForm(f1,f1_ty),fs) -> 
          (try let (_,f_ty,no_of_args_to_consume) = List.find (fun (g,_,_) -> g=f1) constrs in
            if FormUtil.equal_types f1_ty f_ty then
              let (tys, res_ty) = match FormUtil.normalize_type f1_ty with TypeFun (tys, res_ty) -> (tys, res_ty) | ty -> ([], ty) in
              let (consumed_fs, remaining_fs, remaining_tys) = consume no_of_args_to_consume [] fs tys in
              let (replace_map_after_f1,global_env_after_f1,new_f) = replace replace_map global_env bounded_vars f1 consumed_fs in
              let new_f_ty = FormUtil.normalize_type (TypeFun (remaining_tys, res_ty)) in
              (match remaining_fs with
                  [] -> (replace_map_after_f1, global_env_after_f1, (attach_type_if_not_attached new_f res_ty))
                | _ -> 
                    let (replace_map_after_f1_and_args,global_env_after_f1_and_args,new_args) = abst_list replace_map_after_f1 global_env_after_f1 bounded_vars constrs remaining_fs in
                    (replace_map_after_f1_and_args, global_env_after_f1_and_args, (App((attach_type_if_not_attached new_f new_f_ty), new_args))))
            else failwith ("smart_abstract_constructs_in_sequent, subfunction abst_form: to be substituted variable and the variable in the formula have different types "^(PrintForm.string_of_type f_ty)^" and "^(PrintForm.string_of_type f1_ty)^".\n")
          with Not_found -> 
            let (replace_map_after_f1,global_env_after_f1,new_f1) = abst_form replace_map global_env bounded_vars constrs f1 in
            let (new_replace_map,new_global_env,new_fs) = abst_list replace_map_after_f1 global_env_after_f1 bounded_vars constrs fs in
            (new_replace_map, new_global_env, (App((attach_type_if_not_attached new_f1 f1_ty),new_fs))))
      | App(f1,fs) ->
          (try let (_,f_ty,no_of_args_to_consume) = List.find (fun (g,_,_) -> g=f1) constrs in
            let tys, res_ty = match FormUtil.normalize_type f_ty with TypeFun (tys, res_ty) -> (tys, res_ty) | ty -> ([], ty) in
            let (consumed_fs, remaining_fs, remaining_tys) = consume no_of_args_to_consume [] fs tys in
            let (replace_map_after_f1,global_env_after_f1,new_f) = replace replace_map global_env bounded_vars f1 consumed_fs in
            let new_f_ty = FormUtil.normalize_type (TypeFun(remaining_tys,res_ty)) in
            let new_f1 = (match new_f with Var _ -> TypedForm(new_f,new_f_ty) | _ -> new_f) in
            (match remaining_fs with
                [] -> (replace_map_after_f1,global_env_after_f1,new_f1)
              | _ -> 
                  let (new_replace_map,new_global_env,new_args) = abst_list replace_map_after_f1 global_env_after_f1 bounded_vars constrs remaining_fs in
                  (new_replace_map,new_global_env,(App(new_f1,new_args))))
          with Not_found ->
            let (replace_map_after_f1,global_env_after_f1,new_f1) = abst_form replace_map global_env bounded_vars constrs f1 in
            let (new_replace_map,new_global_env,new_fs) = abst_list replace_map_after_f1 global_env_after_f1 bounded_vars constrs fs in
            (new_replace_map,new_global_env,(App(new_f1,new_fs))))
      | Binder(b,til,f1) -> 
          let (freshened_til,updated_f1,shortened_constrs) = List.fold_right
            (fun (curr_bvar,curr_bvar_ty) (sofar_typed_bvar_list,sofar_f1,sofar_constrs) -> 
              let (updated_bvar,updated_form,updated_constrs) = sanitize_single_var curr_bvar sofar_f1 sofar_constrs in
              (((updated_bvar,curr_bvar_ty)::sofar_typed_bvar_list),updated_form,updated_constrs)
            ) til ([],f1,constrs) in
          let new_bounded_vars = typeEnv2mapVarType freshened_til in
          let (new_replace_map,new_global_env,new_f1) = abst_form replace_map global_env (unionMapVarType_preferFirst new_bounded_vars bounded_vars) shortened_constrs f1 in
          (new_replace_map,new_global_env,(Binder(b,freshened_til,new_f1)))
      | TypedForm(f1,ty) -> 
          let (new_replace_map,new_global_env,new_f1) = abst_form replace_map global_env bounded_vars constrs f1 in
          (new_replace_map,new_global_env,(TypedForm(new_f1,ty)))
  and
  (* [abst_list replace_map global_env bounded_vars constrs fs]
     abstracts the formulas in fs by replacing the occurences of symbols in constrs by fresh symbols, taking bounded variables into account. The replacements are stored in replace_map. The types of free variables are given in global_env, the types of bounded variables are given in bounded_vars. The tuple (updated replace map, updated global type environment, new formula list) is returned. *)
      abst_list (replace_map:mapFormForm) (global_env:mapVarType) (bounded_vars: mapVarType) (constrs: (form * typeForm * int) list) (fs:form list) : (mapFormForm*mapVarType*(form list)) =
    List.fold_right 
     (fun curr_f (curr_replace_map,curr_global_env,sofar_f_list) -> 
       let (updated_replace_map,updated_global_env,new_f) = abst_form curr_replace_map curr_global_env bounded_vars constrs curr_f in
       (updated_replace_map,updated_global_env,(new_f::sofar_f_list)))
     fs (replace_map,global_env,[])
  in
    let (repl_map_after_antecedent,global_env_after_antecedent,new_antecedent) = abst_list MapOfForms.empty env MapOfVars.empty constrs antecedent in
    let (_,new_global_env,new_succedent) = abst_form repl_map_after_antecedent global_env_after_antecedent MapOfVars.empty constrs succedent in
    (new_global_env,(new_antecedent,new_succedent))

(** [OrderedType] is the structure for ordered types. *)
module OrderedType = struct
  type t = typeForm
  let compare = compareType   (* Comparison up to the distiction between arrays and functions. *)
  (* Pervasives.compare would be an alternative. *) 
end

(** [MapOfTypes] is the module for maps with the domain of types. *)
(*
module MapOfTypes = Map.Make(OrderedType)
type substTypeString = string MapOfTypes.t
*)

(** [convert_comprehensions_to_vars trm old_bindings]
    In a term trm, converts those comprehensions into set identifiers which are not under a quantifier and have a provably finite type. Old_bindings is a mapping from set comprehensions to identifiers. If in trm a comprehension is encountered which is already bound in old_bindings, then the old identifier is used. If any conversions have been applied to trm, Some (g,sb) is returned, where g is the resulting term and sb is the updated mapping from comprehensions to identifiers.
    If no conversions have been made, None is returned. *)
let rec convert_comprehensions_to_vars (trm:form) (old_bindings:mapFormVar) : ((form*mapFormVar) option) =
  match trm with
      Var _ | Const _ -> None
    | App(f,fl) ->
      let (new_f,bindings_after_f,changed_f) = match convert_comprehensions_to_vars f old_bindings with
	  None -> (f, old_bindings, false)
	| Some (new_f,new_bindings) -> (new_f,new_bindings,true)
      in let (new_fl,new_bindings_after_f_fl,changed_fl) = List.fold_right (fun g (sofar_fl,sofar_bindings,sofar_changed) ->
	match convert_comprehensions_to_vars g sofar_bindings with
	    None -> ((g::sofar_fl),sofar_bindings,sofar_changed)
	  | Some(new_g,new_bindings) -> ((new_g::sofar_fl),new_bindings,true)
      ) fl ([],bindings_after_f,changed_f)
	 in
	 if changed_f then
	   if changed_fl then Some((App(new_f,new_fl)),new_bindings_after_f_fl) else Some((App(new_f,fl)),bindings_after_f)
	 else
	   if changed_fl then Some((App(f,new_fl)),new_bindings_after_f_fl) else None
    | Binder(Comprehension,[],condition) -> Some(Const EmptysetConst, old_bindings)
    | Binder(Comprehension,til,condition) -> 
      (try let (var_name,var_type) = MapOfForms.find trm old_bindings in Some ((TypedForm((Var var_name),var_type)), old_bindings)
       with Not_found ->
	 let type_list = List.map (fun (_,ty) -> ty) til in
	 if is_finite_type_list type_list then
	   (let typeOfVar = (match type_list with [ty] -> FormUtil.mk_set_type ty | _ -> FormUtil.mk_set_type (FormUtil.mk_product_type type_list)) in
	    let fr_name = Util.fresh_name "S" in
	    Some ((FormUtil.mk_typedform((Var fr_name),typeOfVar)),(MapOfForms.add trm (fr_name,typeOfVar) old_bindings)))
	 else None (* Do not do anything with sets over infinite types. *) )
    | Binder(_,_,_) -> None (* do not convert under the quantifiers or lambda abstraction, since we don't need that yet *)
    | TypedForm(((Binder(Comprehension,til,condition)) as cmpr),tf) -> 
      (try let (var_name,var_type) = MapOfForms.find cmpr old_bindings in Some ((TypedForm((Var var_name),tf)), old_bindings)
       with Not_found -> 
	 let fr_name=Util.fresh_name "S" in
	 Some ((FormUtil.mk_typedform((Var fr_name),tf)),(MapOfForms.add trm (fr_name,tf) old_bindings)))
    | TypedForm(f,tf) ->
      (match convert_comprehensions_to_vars f old_bindings with
	  None -> None
	| Some (g,sb) -> Some ((TypedForm(g,tf)),sb))

(** [extract_cardinalities_of_comprehensions_of_term trm old_bindings]
    finds all occurences of terms of the form |... {...} ...| in term trm and returns
    Some (simpler_trm,new_bindings) or None.
    In the "Some" case:
      The term "simpler_trm" is trm, in which each occurence of a finite comprehension under a cardinality has been substituted by a fresh set variable. If two occurences of the comprehension under the cardinality can be easily proven equivalent, they are mapped to the same set variable.
      In addition or instead, some simplifications of trm may occur.
      The map "new_bindings" contains old_bindings and the new substitutions of the occurences of the comprehension by the corresponding fresh set variables.
    In the "None" case: nothing was to extract and nothing to simplify.
*)
let rec extract_cardinalities_of_comprehensions_of_term (t:form) (old_bindings:mapFormVar) : ((form*mapFormVar) option)=
  match t with
      Var _ | Const _-> None
    | App((Const Card) as c, lst) | App((Const Cardeq) as c, lst) | App((Const Cardleq) as c, lst) | App((Const Cardgeq) as c, lst)->
      let (new_lst,new_bindings_lst,changed) = List.fold_right
	(fun g (sofar_lst,sofar_bindings,sofar_changed) ->
	  match convert_comprehensions_to_vars g sofar_bindings with
	      Some (new_g,new_bindings_g) -> ((new_g::sofar_lst),new_bindings_g,true)
	    | None -> ((g::sofar_lst),sofar_bindings,sofar_changed))
	lst ([],old_bindings,false)
      in if changed then Some ((App (c,new_lst)),new_bindings_lst) else None
    | App(f,fl) ->
      let (new_f,bindings_after_f,changed_f) = match extract_cardinalities_of_comprehensions_of_term f old_bindings with
	  None -> (f, old_bindings, false)
	| Some (new_f,new_bindings) -> (new_f,new_bindings,true)
      in let (new_fl,new_bindings_after_f_fl,changed_fl) = List.fold_right (fun g (sofar_fl,sofar_bindings,sofar_changed) ->
	match extract_cardinalities_of_comprehensions_of_term g sofar_bindings with
	    None -> ((g::sofar_fl),sofar_bindings,sofar_changed)
	  | Some(new_g,new_bindings) -> ((new_g::sofar_fl),new_bindings,true)
      ) fl ([],bindings_after_f,changed_f)
	 in
	 if changed_f then
	   if changed_fl then Some((App(new_f,new_fl)),new_bindings_after_f_fl) else Some((App(new_f,fl)),bindings_after_f)
	 else
	   if changed_fl then Some((App(f,new_fl)),new_bindings_after_f_fl) else None
    | Binder(_,_,_) -> None (* Currently do not treat comprehensions outside of cardinalities particularly. *)
    | TypedForm(g,tf) ->
      (match extract_cardinalities_of_comprehensions_of_term g old_bindings with
	  None -> None
	| Some (new_g,new_bindings) -> Some ((TypedForm(new_g,tf)),new_bindings))

(** [extract_cardinalities_of_comprehensions_of_formula f polarity old_bindings]
    finds all occurences of terms of the form |...{...}...| in the formula f which are not under a binder and returns
    Some (simpler_f,approx_f,new_bindings) or None.
    In the "Some" case:
      The formula "simpler_f" is f, in which each free occurence of a finite comprehension under a cardinality which is not under a binder has been substituted by a fresh set symbol.
      The formula "approx_f" is f where each atomic subformula that contains |...{...}...| and is not under a binder has been removed in a way that is sound for
      - unsatisfiability (overapproximating the set of models) if polarity is true,
      - validity (underapproximating the set of models) if polarity is false.
      The map "new_bindings" contains old_bindings and the substitutions of the occurences of |...{...}...| in f by the cardinalities of the corresponding fresh set variables.
    In the "None" case: in f there are no comprehensions under cardinalities outside of binders and f could not be simplified.
*)
let rec extract_cardinalities_of_comprehensions_of_formula (f:form) (polarity:bool) (old_bindings:mapFormVar) : ((form*form*mapFormVar) option)=
  match f with
      Var _ | Const _-> None
    | App((Const Eq) as c, ([g1;g2] as lst)) | App ((Const MetaEq) as c, ([g1;g2] as lst)) -> 
      if (FormUtil.is_bool_form g1) && (FormUtil.is_bool_form g2) then
	(match extract_cardinalities_of_comprehensions_of_formula (App (Const Iff, lst)) polarity old_bindings with
	    None -> None
	  | Some (middle_f,approx_middle_f,new_bindings) ->
	    let new_f = (match middle_f with
		App((Const Iff),middle_lst) -> App(c,middle_lst)
	      | _ -> middle_f ) in
	    let new_approx_f = (match approx_middle_f with
		App((Const Iff),middle_lst) -> App(c,middle_lst)
	      | _ -> approx_middle_f) in
	    Some (new_f,new_approx_f,new_bindings))
      else
	let (new_terms,new_bindings,any_changes) = List.fold_right
	  (fun term (sofar_terms,sofar_bindings,sofar_changed) -> 
	    match extract_cardinalities_of_comprehensions_of_term term sofar_bindings with
		Some (simpler_term,new_bindings) -> ((simpler_term::sofar_terms),new_bindings,true)
	      | None -> ((term::sofar_terms),sofar_bindings,sofar_changed))
	  lst ([],old_bindings,false)
	in if any_changes then Some ((App (Const Eq, new_terms)),(Const (BoolConst polarity)),new_bindings) else None
    | App((Const Or) as c, lst) | App((Const And) as c, lst) | App((Const MetaAnd) as c, lst) | App((Const (BoolConst _)) as c, lst) | App((Const Comment) as c, lst) | App((Const Old) as c, lst) -> (* functions taking boolean formulas and returning boolean formulas without change in polarity *)
      let (new_lst,new_weaker_lst,new_bindings,any_changes) = List.fold_right
	(fun g (sofar_lst,sofar_weaker_lst,sofar_bindings,sofar_changed) -> 
	  match extract_cardinalities_of_comprehensions_of_formula g polarity sofar_bindings with
		Some (simpler_g,weaker_g,new_bindings) -> ((simpler_g::sofar_lst),(weaker_g::sofar_weaker_lst),new_bindings,true)
	      | None -> ((g::sofar_lst),(g::sofar_weaker_lst),sofar_bindings,sofar_changed))
	  lst ([],[],old_bindings,false)
      in if any_changes then Some ((App(c,new_lst)), (App(c,new_weaker_lst)), new_bindings) else None
    | App(((Const Elem) as c), ([_;_] as lst)) | App(((Const Disjoint) as c), lst) | App(((Const Lt) as c), ([_;_] as lst)) | App(((Const Gt) as c), ([_;_] as lst)) | App(((Const LtEq) as c), ([_;_] as lst)) | App(((Const GtEq) as c), ([_;_] as lst)) | App(((Const Cardeq) as c),([_;_] as lst)) | App(((Const Cardleq) as c),([_;_] as lst)) | App(((Const Cardgeq) as c),([_;_] as lst)) | App(((Const ArrayRead) as c),([_;_;_] as lst)) | App(((Const FieldRead) as c),([_;_] as lst)) | App(((Const Subseteq) as c),([_;_] as lst)) | App(((Const Subset) as c),([_;_] as lst)) | App(((Const Seteq) as c),([_;_] as lst)) | App(((Const Let) as c),lst) ->  (* functions taking terms (or functions which we view as taking terms) and returning booleans in some cases. *)
      let (new_lst,new_bindings,any_changes) = List.fold_right
	(fun trm (sofar_lst,sofar_bindings,sofar_changed) -> 
	  match extract_cardinalities_of_comprehensions_of_term trm sofar_bindings with
		Some (simpler_trm,new_bindings) -> ((simpler_trm::sofar_lst),new_bindings,true)
	      | None -> ((trm::sofar_lst),sofar_bindings,sofar_changed))
	  lst ([],old_bindings,false)
      in if any_changes then Some ((App(c,new_lst)), (Const (BoolConst polarity)), new_bindings) else None
    | App((Const Not), [g]) ->
      (match extract_cardinalities_of_comprehensions_of_formula g (not polarity) old_bindings with
	  Some (simpler_g,approx_g,new_bindings) -> Some ((FormUtil.smk_not simpler_g),(FormUtil.smk_not approx_g),new_bindings)
	| None -> None)
    | App(((Const Impl) as c),[ant;cons]) | App(((Const MetaImpl) as c),[ant;cons]) ->
      (match extract_cardinalities_of_comprehensions_of_formula ant (not polarity) old_bindings with
	  Some (simpler_ant,approx_ant,bindings_after_ant) ->
	    (match extract_cardinalities_of_comprehensions_of_formula cons polarity bindings_after_ant with
		Some (simpler_cons,approx_cons,new_bindings) -> Some ((App(c,[simpler_ant;simpler_cons])),(App(c,[approx_ant;approx_cons])),new_bindings)
	      | None -> Some((App(c,[simpler_ant;cons])),(App(c,[approx_ant;cons])),bindings_after_ant))
	| None ->
	  (match extract_cardinalities_of_comprehensions_of_formula cons polarity old_bindings with
	      Some(simpler_cons,approx_cons,new_bindings) -> Some ((App(c,[ant;simpler_cons])),(App(c,[ant;approx_cons])),new_bindings)
	    | None -> None))
    | App((Const Iff),[g1;g2]) -> 
      let i12 = FormUtil.mk_impl (g1,g2) in
      let i21 = FormUtil.mk_impl (g2,g1) in
      (match extract_cardinalities_of_comprehensions_of_formula i12 polarity old_bindings with
	  Some (simpler12,approx12,new_bindings_after12) ->
	    (match extract_cardinalities_of_comprehensions_of_formula i21 polarity new_bindings_after12 with
		Some (simpler21,approx21,new_bindings_after1221) -> 
		  Some ((FormUtil.mk_and [simpler12;simpler21]),(FormUtil.mk_and [approx12;approx21]),new_bindings_after1221)
	      | None -> Some ((FormUtil.mk_and [simpler12;i21]),(FormUtil.mk_and [approx12;i21]),new_bindings_after12))
	| None -> 
	  (match extract_cardinalities_of_comprehensions_of_formula i21 polarity old_bindings with
		Some (simpler21,approx21,new_bindings_after21) -> 
		  Some ((FormUtil.mk_and [i12;simpler21]),(FormUtil.mk_and [i12;approx21]),new_bindings_after21)
	      | None -> None))	  
    | App(Const Ite, [cond;thenpart;elsepart]) ->
      extract_cardinalities_of_comprehensions_of_formula
	(App (Const And, [(App (Const Impl, [cond;thenpart]));(App (Const Impl,[(App (Const Not,[cond]));elsepart]))])) 
	polarity old_bindings
    | App(f,fs) -> 
      (match extract_cardinalities_of_comprehensions_of_term f old_bindings with
	  Some (new_f,bindings_after_f) -> 
	    let (new_fs,bindings_after_f_fs,any_changes) = List.fold_right
	      (fun g (sofar_new_fs,sofar_bindings,sofar_changes) ->
		match extract_cardinalities_of_comprehensions_of_term g sofar_bindings with
		    Some (new_g,bindings_after_g) -> ((new_g::sofar_new_fs),bindings_after_g,true)
		  | None -> ((g::sofar_new_fs),sofar_bindings,sofar_changes)) fs ([],bindings_after_f,false) in
	    if any_changes then
	      Some ((App(new_f,new_fs)),(FormUtil.mk_bool polarity),bindings_after_f_fs)
	    else
	      Some ((App(new_f,fs)),(FormUtil.mk_bool polarity),bindings_after_f)
	| None -> 
	  let (new_fs,bindings_after_fs,any_changes) = List.fold_right
	    (fun g (sofar_new_fs,sofar_bindings,sofar_changes) ->
	      match extract_cardinalities_of_comprehensions_of_term g sofar_bindings with
		  Some (new_g,bindings_after_g) -> ((new_g::sofar_new_fs),bindings_after_g,true)
		| None -> ((g::sofar_new_fs),sofar_bindings,sofar_changes)) fs ([],old_bindings,false) in
	  if any_changes then Some ((App(f,new_fs)),(FormUtil.mk_bool polarity),bindings_after_fs) else None)
    | Binder(_,_,_) -> None (* Currently leaving cardinalities of comprehensions under a quantifier as they are. *)
    | TypedForm(frm,(TypeApp(TypeBool,[]))) ->
      (match extract_cardinalities_of_comprehensions_of_formula frm polarity old_bindings with
	  Some (simpler_frm,approx_frm,new_bindings) -> Some (TypedForm(simpler_frm,(TypeApp(TypeBool,[]))),TypedForm(approx_frm,(TypeApp(TypeBool,[]))),new_bindings)
	| None -> None)
    | TypedForm(_,_) -> failwith (("A formula should be boolean, but it is not:\n"^(PrintForm.string_of_form f)^".\n"))

(** extract_cardinalities_of_comprehensions_of_sequent sq
    finds all occurences of terms of the form |...{...}...| that are not under a binder in the sequent sq=(ant,cons) and returns
    (simpler_sq,approx_sq,bindings)
    The sequent "simpler_sq" is sq, in which each occurence of a finite comprehension under a cardinality, but not under a binder, has been substituted by a fresh set symbol.
    The sequent "approx_sq" is built from sq, where each atomic subformula that contains |...{...}...| that is not under a binder has been removed in a way
      such that (approx_sq => sq) is valid.
    The map "bindings" contains the substitution of the occurences of comprehensions under cardinalities, but not under binders, by the corresponding fresh set variables.
*)
let extract_cardinalities_of_comprehensions_of_sequent ((asms,cons):sequent) : (sequent*sequent*mapFormVar) option =
  let (simpler_asms,approx_asms,asm_bindings,changed) = 
    List.fold_right 
      (fun curr_asm (sofar_asms,sofar_approx,sofar_bindings,sofar_changed) -> 
	match extract_cardinalities_of_comprehensions_of_formula curr_asm true sofar_bindings with
	    Some (simpler_asm,approx_asm,new_bindings) -> ((simpler_asm::sofar_asms),(approx_asm::sofar_approx),new_bindings,true)
	  | None -> ((curr_asm::sofar_asms),(curr_asm::sofar_approx),sofar_bindings,sofar_changed))
      asms ([],[],MapOfForms.empty,false) in
  if changed then 
    match extract_cardinalities_of_comprehensions_of_formula cons false asm_bindings with
	Some (simpler_cons,approx_cons,new_bindings) -> 
	  Some ((simpler_asms,simpler_cons),(approx_asms,approx_cons),new_bindings)
      | None -> Some ((simpler_asms,cons),(approx_asms,cons),asm_bindings)
  else 
    match extract_cardinalities_of_comprehensions_of_formula cons false MapOfForms.empty with
	Some (simpler_cons,approx_cons,new_bindings) ->
	  Some ((asms,simpler_cons),(asms,approx_cons),new_bindings)
      | None -> None
