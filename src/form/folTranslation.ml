open Common
open Form
open FormUtil
open Printf

(** Perform translation from formulas of type [Form.form] and first-order logic. 

    The aim is to use fast 1st-order automatic theorem provers. 

    @author Charles Bouillaguet (charles.bouillaguet@dptinfo.ens-cachan.fr) *)


let debug_msg = 
  let reg = Debug.register_debug_module "TPTP" in
    fun l s -> Debug.debug_lmsg reg l (fun () -> s)

(* let translation_mode = ref (`Predicates) *)
let translation_mode = ref (`Function_symbols) 


module StringSet = Set.Make(String) 

(** {6 the new datastructure type } *)

type basesort = [`I | `O | `F | `B | `Unknown | `Tuple of basesort list]
type sort = [basesort |  `Set of basesort]

let sort : basesort -> sort = function
  | s -> (s :> sort)

type ident = string
type vo_t = [`Vo of ident | `Null | `Int of int | `BeingTrue | `BeingFalse] (** Object-valued variable or constant. *)
type vs_t = [`Vs of ident ] (** Set-valued variable *)
type ofv_t = [`Fo of ident] (** Object-valued field-Variable *)
type sfv_t = [`Fs of ident] (** Set-valued field-Variable *)

type boool = [`True | `False | `BoolVar of ident  | `NegatedBoolVar of ident] (** boolean value *)

type a_state = [`ArrayStateVar of ident | `ArrayWrite of a_state * o_t * o_t * o_t]
and o_t = [vo_t | `VoVf of o_t*of_t | `Fun of ident*((o_t*basesort) list) | `ArrayRead of a_state * o_t * o_t | `Tuple_o of (o_t*basesort) list] 
and of_t =  [ofv_t | `FieldWrite_o of of_t*o_t*o_t] (** Object-valued field*)

type sf_t = [sfv_t | `FieldWrite_s of sf_t*o_t*s_t] (** Set-valued field*)
and s_t = [ vs_t | `VsVf of o_t*sf_t | `Intersection of s_t*s_t | `Union of s_t*s_t | `Difference of s_t*s_t | `FiniteSet of o_t list | `UniversalSet | `Comprehension of o_t->fol_form_t ] 

(** Set expression. Boolean algebra, field deference and variables *)

and atom_t = [
| `Eq_o of o_t*o_t 
| `Eq_s of s_t*s_t 
| `MemberShip of o_t*s_t 
| `Inclusion of s_t*s_t 
| `Eq_of of of_t*of_t 
| `Eq_sf of sf_t*sf_t  
| `CardConstr of s_t*int (** the set has at most k elements *)
| `Relation of ident*(o_t* basesort) list 
] (** atomic formula *)

and fol_form_t = [
| `Atom of sort * atom_t 
| boool 
| `Negation of fol_form_t 
| `Conjunction of fol_form_t list 
| `Disjunction of fol_form_t list 
| `Implication of fol_form_t*fol_form_t 
| `Equivalence of fol_form_t*fol_form_t 
| `Forall of (ident*basesort) list*fol_form_t
| `Exists of (ident*basesort) list*fol_form_t
]  (** formula with unbounded quantification over OBJECTS only *)


(** now the types for 1st order formulas*)

type term = basesort * [`Int of int | `Constant of ident | `Variable of ident | `Function of ident*(term list) ]
type fol_atom = [`Predicate of ident*(term list) | `Equality of term*term]
type fol_formula = [
  boool 
| fol_atom
| `Negation of fol_formula 
| `Conjunction of fol_formula list 
| `Disjunction of fol_formula list 
| `Exists of (ident*basesort) list * fol_formula 
| `Forall of (ident*basesort) list * fol_formula]


type unnesting_mode = Existential | Universal

(* nasty imperativ feature *)
type sort_env = (string, basesort) Hashtbl.t
let sort_env = Hashtbl.create 100
let set_sort = Hashtbl.replace sort_env

type sort_env_sets = (string, basesort) Hashtbl.t
let sort_env_sets = Hashtbl.create 100
let set_sort_set = Hashtbl.replace sort_env_sets

type sort_env_setf = (string, basesort) Hashtbl.t
let sort_env_setf = Hashtbl.create 100
let set_sort_setf = Hashtbl.replace sort_env_setf


(** raise [Failure] with a small message (containing [s]) showing the formula [f]. *)
let nice_fail (m:string) (f:Form.form) : 'a = 
  let s =  ((sprintf "\n\nFOL Translation Panic [%s] : (%s)\n\nOr, more readable : \n%s\n" m (MlPrintForm.string_of_form (unlambda f)) (PrintForm.string_of_form (unlambda f))) ^ 
  (match f with
    | App (Const c , blabla) -> sprintf "%s and then \n%s\n" (string_of_const c) (String.concat "\n" (List.map MlPrintForm.string_of_form blabla))
    | f -> ""
  )) in
    Util.msg s;
    failwith (sprintf "\n\nFOL Translation Panic [%s]" m)

let rec sort_set_name : basesort -> string= function
  | `O -> "Object"
  | `I -> "Integer"
  | `B -> "Boolean"
  | `F -> "Float"
  | `Unknown -> "Unknown"
  | `Tuple l -> String.concat "_x_" (ListLabels.map ~f:sort_set_name l)

let sort_name : sort -> string = function
  | `Set s -> "Set of " ^ sort_set_name s
  | #basesort as s -> sort_set_name s


let switch_bool : boool -> boool = function
  | `True -> `False
  | `False -> `True
  | `BoolVar v -> `NegatedBoolVar v
  | `NegatedBoolVar v -> `BoolVar v

(** [fresh_ident s] generates a fresh identifier whose name contains [s]. *)
let fresh_ident : string -> string = fun s -> Util.fresh_name (s ^ "_foltrans")

type vars = ident list

let rec fv (f : fol_form_t) : vars = 
  let rec fv_o (* : (o_t -> vars) *) = function
    | `Vo v' -> [v']
    | `VoVf (o, f) -> fv_o o @ fv_of f
    | `Fun (f, args) -> [f] @ List.concat (List.map fv_o1 args)
    | `Tuple_o (args) -> List.concat (List.map fv_o1 args)
    | `ArrayRead (s,a,i) -> fv_a s @ fv_o a @ fv_o i
    | _ -> []

  and fv_o1 (o,_) = fv_o o
	
  and fv_s : s_t -> vars = function
    | `VsVf (o, f) -> fv_o o @ fv_sf f
    | `Vs x -> [x]
    | `Intersection (s1,s2) 
    | `Union (s1,s2) 
    | `Difference (s1,s2) -> fv_s s1 @ fv_s s2
    | `FiniteSet args -> List.concat (List.map fv_o args)
    | `UniversalSet -> []
    | `Comprehension fn -> fv_f (fn (`Vo "_dummy_name_folTranslation"))
(*    | _ -> [] *)

  and fv_a (* : (a_state -> vars) *) = function
    | `ArrayStateVar v -> [v]
    | `ArrayWrite (s, a, i, c) -> fv_a s @ fv_o a @ fv_o i @ fv_o c
(*    | _ -> [] *)
	
  and fv_f = function
    | `Atom (s, a) -> (match a with
			       | `Eq_o (a, b) -> fv_o a @ fv_o b 
			       | `Eq_s (a, b) -> fv_s a @ fv_s b
			       | `MemberShip (a, b) -> fv_o a @ fv_s b
			       | `Inclusion (a, b) -> fv_s a @ fv_s b
			       | `CardConstr (s, k) -> fv_s s
			       | `Eq_of (f1, f2) -> fv_of f1 @ fv_of f2
			       | `Eq_sf (f1, f2) -> fv_sf f1 @ fv_sf f2
			       | `Relation (f, args) -> List.concat (List.map fv_o1 args))
(*			       | _ -> []) *)
    | `Negation f1 -> fv_f f1 
    | `Conjunction fs -> List.concat (List.map fv_f fs)
    | `Disjunction fs -> List.concat (List.map fv_f fs)
    | `Implication (f1,f2) -> fv_f f1 @ fv_f f2
    | `Equivalence (f1,f2) -> fv_f f1 @ fv_f f2
    | `Forall (vs, f) -> Util.difference (fv_f f) (fst (List.split vs))
    | `Exists (vs, f) -> Util.difference (fv_f f) (fst (List.split vs))
    | _ -> []

  and fv_of (* : (of_t -> vars) *) = function
    | `FieldWrite_o (f, o1, o2) -> fv_of f @ fv_o o1 @ fv_o o2
    | `Fo x -> [x]
(*    | _ -> [] *)

  and fv_sf (* : (sf_t -> vars) *) = function
    | `FieldWrite_s (f, o, s) -> fv_sf f @ fv_o o @ fv_s s
    | `Fs x -> [x]
(*    | _ -> [] *)
  in
    fv_f f

(** replaces the object variable [v] by the object [o] in [f]. [v] is supposed not to be bound in [f] (exception thrown otherwise).
    No type-checking is done --> you are responsible !*)
let subst ~(v:ident) ~(o:o_t) f : fol_form_t = 
  let rec fvo = fv f

  and subst_o (* : o_t -> o_t *) = function
    | `Vo v' when v' = v -> o
    | `VoVf (o, f) -> `VoVf (subst_o o, subst_of f)
    | `Fun (f, args) -> `Fun (f, ListLabels.map ~f:(fun (o,s) -> (subst_o o, s)) (args:(o_t*basesort) list))
    | `Tuple_o (args) -> `Tuple_o (ListLabels.map ~f:(fun (o,s) -> (subst_o o, s)) (args:(o_t*basesort) list))
    | `ArrayRead (s,a,i) -> `ArrayRead (subst_a s, subst_o a, subst_o i)
    | o -> o
	
  and subst_s (* : s_t -> s_t *) = function
    | `VsVf (o, f) -> `VsVf (subst_o o, subst_sf f)
    | `Intersection (s1,s2) -> `Intersection (subst_s s1,subst_s s2)
    | `Union (s1,s2) -> `Union (subst_s s1,subst_s s2)
    | `Difference (s1,s2) -> `Difference (subst_s s1,subst_s s2)
    | `FiniteSet args -> `FiniteSet (List.map subst_o args)
    | `Comprehension fn -> `Comprehension (fun x -> subst_f (fn x))
    | s -> s

  and subst_a (* : a_state -> a_state *) = function
    | `ArrayStateVar v -> `ArrayStateVar v
    | `ArrayWrite (s, a, i, c) -> `ArrayWrite (subst_a s, subst_o a, subst_o i, subst_o c)
	
  and subst_f (* : fol_form_t -> fol_form_t *)  = function
    | `Atom (s, a) -> `Atom (s, match a with
			       | `Eq_o (a, b) -> `Eq_o (subst_o a, subst_o b)
			       | `Eq_s (a, b) -> `Eq_s (subst_s a, subst_s b)
			       | `MemberShip (a, b) -> `MemberShip (subst_o a, subst_s b)
			       | `Inclusion (a, b) -> `Inclusion (subst_s a, subst_s b)
			       | `CardConstr (s, k) -> `CardConstr (subst_s s, k)
			       | `Eq_of (f1, f2) -> `Eq_of (subst_of f1, subst_of f2)
			       | `Eq_sf (f1, f2) -> `Eq_sf (subst_sf f1, subst_sf f2)
			       | `Relation (f, args) ->  `Relation (f, ListLabels.map ~f:(fun (o, s) -> (subst_o o, s)) args)
			    )
    | `Negation f -> `Negation (subst_f f)
    | `Conjunction fs -> `Conjunction (ListLabels.map subst_f fs)
    | `Disjunction fs -> `Disjunction (ListLabels.map subst_f fs)
    | `Implication (f1,f2) -> `Implication (subst_f f1, subst_f f2)
    | `Equivalence (f1,f2) -> `Equivalence (subst_f f1, subst_f f2)
    | `Forall (vs, f) when ListLabels.mem ~set:(fst (List.split vs)) v -> `Forall (vs, f)  (* no change *) 
    | `Exists (vs, f) when ListLabels.mem ~set:(fst (List.split vs)) v -> `Exists (vs, f)  (* no change *)
    | `Forall (vs, f) when not (Util.disjoint (fst (List.split vs)) fvo) -> 
	failwith "capture in substitution [foltranslation.ml]"
    | `Exists (vs, f) when not (Util.disjoint (fst (List.split vs)) fvo) -> 
	failwith "capture in substitution [foltranslation.ml]"
    | `Forall (vs, f) -> `Forall (vs, subst_f f) 
    | `Exists (vs, f) -> `Exists (vs, subst_f f) 
    | #boool as b -> b

  and subst_of (*: of_t -> of_t*) = function
    | `FieldWrite_o (f, o1, o2) -> `FieldWrite_o (subst_of f, subst_o o1, subst_o o2)
    | f -> f

  and subst_sf (*: sf_t -> sf_t *) = function
    | `FieldWrite_s (f, o, s) -> `FieldWrite_s (subst_sf f, subst_o o, subst_s s)
    | f -> f
  in
    subst_f f

(** {6 translation from formulas of type [Form.form] to [fol_form_t]} 

    Not all the constructs of [Form.form] are handled. In particular, all of these functions expect types annotations to be present. This is the case if
    {!TypeReconstruct.reconstruct_types}. They also expect the formula to be disambiguated by {!TypeReconstruct.disambiguate}, and to be in NNF. The last condition
    can be achieved by a call to {!FormUtil.negation_normal_form}. When an unhandled construction appear in the formulas given in argument, a conservative (sound) 
    over-approximation is done : the subformula is replaced by [false] if it occured positively, and by [true] if it occured negatively.
*)

type type_env = (string * typeForm) list


(** Main entry point. [oa] is the Over Approximation mode : this bool value will be returned if the formula can't be translated *)
let rec form ~(oa:boool) ~(env:type_env) ~(doom_mode:bool) (f:Form.form) : fol_form_t = 

(*  let rec basesort_of_simpletype : simpleType -> basesort = function
    | TypeObject -> `O
    | TypeInt -> `I
    | TypeBool -> `B
    | st -> Util.warn ("type2form failed on type : " ^ PrintForm.string_of_form (TypedForm (Const Eq, TypeApp(st, []) ))); `Unknown   in
*)

  let rec basesort_of_type : typeForm -> basesort = function
	| TypeApp (TypeObject, []) -> `O
	| TypeApp (TypeInt, []) -> `I
	| TypeApp (TypeBool, []) -> `B
	| TypeProd l -> `Tuple (ListLabels.map ~f:basesort_of_type l)
	| TypeApp(TypeSet, [t]) -> failwith "Set is NOT a basesort"
	| t -> (* Util.warn ("type2form failed on type : " ^ PrintForm.wr_type t); *) `Unknown
  in
  let sort_of_type : typeForm -> sort = function
	| TypeApp(TypeSet, [t]) -> `Set (basesort_of_type t)
	| t -> sort (basesort_of_type t)
  in
    
  let look_for_basesort (s:string) : basesort =
    try basesort_of_type (List.assoc s env) 
    with Not_found -> `Unknown
  in

  let look_for_sort (s:string) : sort =
    try sort_of_type (List.assoc s env) 
    with Not_found -> `Unknown
  in

  let merge_basesort (s1:basesort) : basesort -> basesort = function
    | `Unknown -> s1
    | s -> s
  in

  let merge_sort (s1:sort) : sort -> sort = function
    | `Unknown -> s1
    | `Set `Unknown -> s1
    | s -> s
  in

let rec object_valued_field : Form.form -> of_t*basesort = function
  | TypedForm (o, t) -> typed_object_valued_field (o,t)
  | Var x -> `Fo x, `Unknown
  | App (Const FieldWrite, [field ; obj ; new_value]) -> 
      let nv, s = obj_value new_value in
	`FieldWrite_o (fst (object_valued_field field), fst (obj_value obj), nv), s
  | f -> nice_fail "I can't handle this object-valued field" f

and typed_object_valued_field : Form.form*Form.typeForm -> of_t*basesort = function
  | of_, TypeFun ([TypeApp (TypeObject, [])], t) 
  | of_, TypeApp (TypeArray, [TypeApp (TypeObject, []); t ]) -> fst (object_valued_field of_), basesort_of_type t

  | o, t -> nice_fail "unknow type for object-valued field" (TypedForm (o,t))

and set_valued_field : Form.form -> sf_t*sort = function
  | TypedForm (o, t) -> typed_set_valued_field (o,t)
  | Var x -> `Fs x, `Set `Unknown
  | App (Const FieldWrite, [field ; obj ; new_value]) -> 
      let nv, s = set_value new_value in
	`FieldWrite_s (fst (set_valued_field field), fst (obj_value obj), nv), s
  | f -> nice_fail "I can't handle this set-valued field" f

and typed_set_valued_field : Form.form*Form.typeForm -> sf_t*sort = function 
  | sf_, TypeFun ([TypeApp (TypeObject, [])], TypeApp (TypeSet, [t])) 
  | sf_, TypeApp (TypeArray, [TypeApp (TypeObject, []); TypeApp (TypeSet, [t])])  -> fst (set_valued_field sf_), `Set (basesort_of_type t)

  | s, t -> nice_fail "unknow type for set-valued field" (TypedForm (s,t))

and array_state_value :  Form.form -> a_state * basesort = function
  | Var v -> `ArrayStateVar v, `Unknown
  | App (Const ArrayWrite, [astate; aname; index; content]) -> 
            let nv, s = obj_value content in
	      `ArrayWrite (fst (array_state_value astate), fst (obj_value aname), fst (obj_value index), nv), s

  | TypedForm (a, _) -> array_state_value a   (* TODO : improve that *)
  | f -> nice_fail "couldn't understand Global Array State Value" f

and obj_value : Form.form -> o_t * basesort = function
  | Const (BoolConst true) -> `BeingTrue, `B
  | Const (BoolConst false) -> `BeingFalse, `B

  | Var x  -> `Vo x, look_for_basesort x
  | Const NullConst -> `Null, `O
  | Const (IntConst n) -> `Int n, `I
  | TypedForm (o,t) -> typed_obj_value (o,t)

  (* handle fieldwrite applied to an element (BAD) *)
  | App (TypedForm(App (Const FieldWrite, args1), _), args2) 
  | App (App (Const FieldWrite, args1), args2) -> 
      obj_value (App (Const FieldRead, App (Const FieldWrite, args1) :: args2)) 

(* handle arraywrite applied to an element (BAD) *)
  | App (TypedForm(App (Const ArrayWrite, args1), _), args2) 
  | App (App (Const ArrayWrite, args1), args2) -> 
      obj_value (App (Const ArrayRead, App (Const ArrayWrite, args1) :: args2)) 


  | App (TypedForm(Const Tuple, _), l) 
  | App (Const Tuple, l) -> 
      let args = ListLabels.map ~f:obj_value l in
      let _, sorts = List.split args in
	`Tuple_o args, `Tuple sorts

  | App (Const ArrayRead, [arraystate ; array_name ; index]) -> 
      let asv, s = array_state_value arraystate in
      `ArrayRead (asv, fst (obj_value array_name), fst (obj_value index)), s

  | App (Const FieldRead, [field; obj]) ->
      let fv, s = object_valued_field field in
	`VoVf (fst (obj_value obj), fv), s

  (* grr... *)
  | App (Const FieldWrite, [field; obj1; content; obj2]) -> 
      obj_value (App (Const FieldRead, [App (Const FieldWrite, [field; obj1; content]); obj2] ))

  | App (Const ArrayWrite, [array_state; array1; i1; content; array2; i2]) -> obj_value (App (Const ArrayRead, [App (Const ArrayWrite, [array_state; array1; i1; content]); array2; i2] ))


  | App (Var "intplus", [f1;f2]) 
  | App (TypedForm(Var "intplus", _), [f1;f2]) 
  | App (Const Plus, [f1; f2]) -> `Fun ("plus", List.map obj_value [f1 ; f2]), `I
  | App (Const UMinus, args) -> `Fun ("uminus", List.map obj_value args), `I
  | App (Const Minus, args) -> `Fun ("minus", List.map obj_value args), `I
  | App (Const Mult, args) -> `Fun ("times", List.map obj_value args), `I
  | App (Const Mod, args) -> `Fun ("mod", List.map obj_value args), `I
  | App (Const Div, args) -> `Fun ("div", List.map obj_value args),`I

(* uninterpreted function application *)
  | App (TypedForm(Var f, TypeFun (_, t)), args) ->
      `Fun (f, ListLabels.map ~f:(fun f -> obj_value f) args), basesort_of_type t

  | App (TypedForm(Var f, (TypeApp(TypeArray, [_; t]))), args) -> 
      `Fun (f, ListLabels.map ~f:(fun f -> obj_value f) args), basesort_of_type t

  | App (TypedForm(Var _, _), args) as f -> nice_fail "strange type" f

  | App (Var f, args) -> 
      let s = 
	try 
	  match List.assoc f env with
	    | TypeFun (_, t) 
	    | TypeApp (TypeArray, [_; t]) -> basesort_of_type t
	    | _ -> nice_fail "strange type" (Var f)
	with Not_found ->
	  Util.warn ("Cannot find type of function " ^ f ^ ". This is likely to cause further trouble"); `Unknown
      in
	`Fun (f, ListLabels.map ~f:(fun f -> obj_value f) args), s

  | f -> nice_fail "unknow object value" f

and typed_obj_value : Form.form*Form.typeForm -> o_t*basesort = function
  | o, TypeApp(TypeSet, _) -> nice_fail "Object expected, but set found..." o
  | o, t -> let s = basesort_of_type t and (v, s') = obj_value o in
      (v,merge_basesort s' s)

and set_value (f:Form.form) : s_t*sort = 
  let result,s  = match f with
    | Var x  -> `Vs x, look_for_sort x
    | Const EmptysetConst -> `FiniteSet [], `Set `Unknown
    | Const UniversalSetConst -> `UniversalSet, `Set `Unknown
    | App (Const Cap, [s1; s2]) -> let sv1, s = set_value s1 in `Intersection (sv1, fst (set_value s2)), s
    | App (Const Cup, [s1; s2]) -> let sv1, s = set_value s1 in `Union (sv1, fst (set_value s2)), s
    | App (Const Diff, [s1; s2]) -> let sv1, s = set_value s1 in `Difference (sv1, fst (set_value s2)), s
    | App (Const FiniteSetConst, []) -> `FiniteSet [], `Set `Unknown
    | App (Const FiniteSetConst, x::tail) -> 
	let v1, s = obj_value x in
	  `FiniteSet (v1::(ListLabels.map ~f:(fun x -> fst (obj_value x)) tail)), (`Set s)
	    
    | TypedForm (s,t) -> typed_set_value (s,t)
	
    | App (field, [obj]) 
    | App (Const FieldRead, [field; obj]) -> 
	let fv, s = set_valued_field field in
	  `VsVf (fst (obj_value obj), fv), s
	    
    | Binder (Comprehension, [(v,t)], f) -> 
	(try 
	   let _, s = obj_value (TypedForm (Var v, t)) in
	   let f' = form ~doom_mode:true ~env ~oa:(`BoolVar (fresh_ident "set_compr")) f in
	     `Comprehension (fun o -> subst ~v ~o f'), `Set s
	 with
	   | Failure m -> nice_fail (m ^ " (in set comprehension)") f
	)
	  
    | f -> nice_fail "I don't understand this set-value" f
  in
    match s with
      | `Set _ -> (result, s)
      | __ -> nice_fail (sprintf "set_value is returning a non-set sort (%s) !!!!" (sort_name s)) f;




and typed_set_value : Form.form*Form.typeForm -> s_t*sort = function
  | set, t -> 
      let v, s' = set_value set and s = sort_of_type t in
	(v, merge_sort s s')

and lteq_bool_value (lhs : Form.form) (rhs : Form.form) : fol_form_t = 
  match lhs, rhs with
  | TypedForm(x1,t1), x2 -> lteq_bool_value x1 x2
  | x1, TypedForm(x2,t2) -> lteq_bool_value x1 x2
  | App(TypedForm(Const Card,_), [se]), x2 -> 
      lteq_bool_value (App(Const Card, [se])) x2
  | App(Const Card, [setF]), intF -> 
      cardleq setF intF
  | x1, x2 -> `Atom (`B, `Relation ("lteq", ListLabels.map ~f:obj_value [x1;x2]))

and bool_value : Form.form -> fol_form_t = function
  | Var v -> `BoolVar v
  | App (Const LtEq, [x1; x2]) -> lteq_bool_value x1 x2
  | App (Const GtEq, [x1; x2]) -> lteq_bool_value x2 x1

  | App (TypedForm(Var "intless", _), [x1; x2]) 
  | App (Var "intless", [x1; x2]) 
  | App (Const Lt, [x1; x2]) -> 
      form ~oa ~env ~doom_mode 
	(App(Const And, [App(Const LtEq, [x1; x2]); 
			 mk_neq(x1,x2)]))

  | App (Const Gt, [x1; x2]) -> bool_value (App (Const Lt, [x2; x1]))

  | App (TypedForm(Var x, _), args) 
  | App (Var x, args) -> `Atom (`B,`Relation (x, ListLabels.map ~f:obj_value args))
  | TypedForm (f, _) -> bool_value f
  | Const (BoolConst true) -> `True
  | Const (BoolConst false) -> `False
  | App (Const FieldRead, [field; obj]) ->
      let fv, _ = object_valued_field field in
	`Atom (`B, `Eq_o (`BeingTrue, `VoVf (fst (obj_value obj), fv)))

(* grrr again *)
  | App (TypedForm(App (f, args1), _), args2) 
  | App (App (f, args1), args2) -> bool_value (App (f, args1 @ args2))

  | App (Const FieldWrite, [field; obj1; content; obj2]) -> bool_value (App (Const FieldRead, [App (Const FieldWrite, [field; obj1; content]); obj2] ))

  | f -> nice_fail "I don't understand this boolean value" f

and cardleq (setF : Form.form) (intF : Form.form) : fol_form_t = 
  match intF with
    | Const (IntConst k) -> 
	let sv, s = set_value setF in 
	  `Atom (s, `CardConstr (sv, k))
    | TypedForm(intF1,_) -> cardleq setF intF1
    | f -> nice_fail "I don't understand cardinality bound" f

in
(* code for form. *)
  try 
    (match f with
       | Binder (Exists, vars, f) -> 
	   let v' = ListLabels.map ~f:(fun (v,t) -> v, snd (obj_value (TypedForm (Var v, t)))) vars in
	     `Exists (v', form ~doom_mode ~env ~oa f)
	       
       | Binder (Forall, vars, f) -> 
	   let v' = ListLabels.map ~f:(fun (v,t) -> v, snd (obj_value (TypedForm (Var v, t)))) vars in
	     `Forall (v', form ~doom_mode ~env ~oa f)
	
       | App (Const Comment, [_; f]) -> form f ~doom_mode ~oa ~env
       
       | (Binder (Lambda,_, _) as f)-> nice_fail "lambda will NEVER be supported" f
       | App (Const MetaAnd, fs) -> `Conjunction (ListLabels.map ~f:(form ~doom_mode ~env ~oa) fs)
       | App (Const And, fs) -> `Conjunction (ListLabels.map ~f:(form ~doom_mode ~env ~oa) fs)
       | App (Const Or, fs) -> `Disjunction (ListLabels.map ~f:(form ~doom_mode ~env ~oa)  fs)
       | App (Const Not, [f]) -> `Negation (form ~oa:(switch_bool oa) ~doom_mode ~env f)
	   
       | (App (Const Subseteq, [TypedForm (_, t1); TypedForm (_, t2)]) as f) 
       | (App (Const Seteq, [TypedForm (_, t1); TypedForm (_, t2)]) as f)
       | (App (Const Eq, [TypedForm (_, t1); TypedForm (_, t2)]) as f) when t1 <> t2 -> nice_fail "equality with differents types on each side !" f
	   
       | App (Const Eq, [f1; f2]) -> 
	   let nv, s = obj_value f1 
	   and nv2, s2 = obj_value f2 in 
	     `Atom(sort (merge_basesort s s2), `Eq_o (nv , nv2))

       | App (Const Seteq, [f1; f2]) -> let v1, s1 = set_value f1 
					and v2, s2 = set_value f2 in
	   `Atom(merge_sort s1 s2, `Eq_s (v1 , v2))

       | App (Const Elem, [o; set]) -> let nv, s = obj_value o in `Atom(sort s, `MemberShip (nv , fst (set_value set)))
	   
(* subset or equal*)
       | App (Const Subseteq, [TypedForm (s1, t1); TypedForm (s2, t2)]) as f when t1<>t2 -> nice_fail "set inclusion with 2 different types" f
       | App (Const Subseteq, [s1; s2]) -> let nv, s = set_value s1 in `Atom(s, `Inclusion (nv , fst (set_value s2)))

(* strict subset *)
       | App (Const Subset, [TypedForm (s1, t1); TypedForm (s2, t2)]) as f when t1<>t2 -> nice_fail "set inclusion with 2 different types" f
       | App (Const Subset, [s1; s2]) -> let nv, s = set_value s1 in 
	   `Conjunction [
	     `Atom(s, `Inclusion (nv , fst (set_value s2)));
	     `Negation (`Atom(s, `Eq_s (nv , fst (set_value s2))))
	   ]


       (* special cases ... *)
       | App (Const Cardleq, [s; Const (IntConst 0)])
       | App (Const Cardeq, [s; Const (IntConst 0)]) -> form ~doom_mode ~env ~oa ( App (Const Seteq, [s;  App (Const FiniteSetConst, [])] ))
       | App (Const Cardgeq, [s; Const (IntConst 0)]) -> `True

       | App (Const Cardeq, [s;k]) -> form ~doom_mode ~env ~oa ( App (Const And, [App (Const Cardleq, [s;k]);  App (Const Cardgeq, [s;k])]))
       | App (Const Cardgeq, [s;k]) -> nice_fail "cardeq not handled yet" f
       | App (Const Cardleq, [setF; intF]) -> cardleq setF intF
   
       | TypedForm (f, _) -> form ~oa f ~env ~doom_mode

       | App (Var "pointsto", [a;f;b]) -> 
	   let x = fresh_ident "pto" in
	     `Forall ([x, `O], `Implication (`Atom(`O, `MemberShip (`Vo x, fst (set_value a))), `Atom (`O, `MemberShip (`VoVf (`Vo x, fst (object_valued_field f)), fst (set_value b)))))

       | f -> bool_value f
    )
  with
    | Failure m when doom_mode -> failwith m
    | Failure m -> Util.msg m ; (oa :> fol_form_t)

(** {6 backward conversion : from the internal represntation to the nasty common representation}*)

let rec backward_conversion_t : term -> Form.form = function
  | _, `Int k -> Const (IntConst k)
  | _, `Variable v 
  | _, `Constant v -> Var v
  | _, `Function (f, args) -> App (Var f, ListLabels.map ~f:backward_conversion_t args)
   
let rec backward_conversion_f : fol_formula -> Form.form = function
  | `True -> Const (BoolConst true)
  | `False -> Const (BoolConst false)
  | `BoolVar v -> Var v
  | `NegatedBoolVar v -> App (Const Not, [Var v])
  | `Equality (a,b) -> App (Const Eq, [backward_conversion_t a ; backward_conversion_t b])
  | `Predicate (p,args) -> App (Var p, ListLabels.map ~f:backward_conversion_t args)
  | `Negation f -> App (Const Not, [backward_conversion_f f])
  | `Conjunction fs -> App (Const And, ListLabels.map ~f:backward_conversion_f fs)
  | `Disjunction fs -> App (Const Or, ListLabels.map ~f:backward_conversion_f fs)
  | `Exists (vars, f) -> Binder (Exists, ListLabels.map ~f:(fun (v,s) -> (v, TypeUniverse)) vars, backward_conversion_f f)
  | `Forall (vars, f) -> Binder (Forall, ListLabels.map ~f:(fun (v,s) -> (v, TypeUniverse)) vars, backward_conversion_f f)

let switch_mode = function
  | Existential -> Universal
  | Universal -> Existential

(** generate a finite set of [k] fresh object variables *)
let rec generate_finite_set : int -> [`Vo of ident] list = function
  | 0 -> []
  | k -> (`Vo (fresh_ident "CardConstr")) :: generate_finite_set (k-1)

let rec generate_big_and_1 ~(set : s_t) (vars : o_t list) : [< `Conjunction of [ `MemberShip of o_t * s_t ] list ] =
    `Conjunction (ListLabels.map ~f:(fun x -> `MemberShip (x, set)) vars)
      
let rec generate_big_and_2 ~(vars:o_t list) : [ `Conjunction of [< `Negation of [ `Eq_o of o_t * o_t ] ] list ]  = 
  let foo (left:o_t) (set:o_t list) : [ `Negation of [ `Eq_o of o_t * o_t ]] list = 
    ListLabels.map ~f:(fun right -> `Negation (`Eq_o (left, right))) set
  in
  let rec bar : o_t list -> [ `Negation of [ `Eq_o of o_t * o_t ]] list = function
    | x::y::[] -> foo x (y::[])
    | x::y::suite -> foo x (y::suite) @ bar (y::suite)
    | _ -> assert false
  in
    `Conjunction (bar vars)

type atom_no_card = 
    [ `Eq_o of o_t * o_t
    | `Eq_of of of_t * of_t
    | `Eq_s of s_t * s_t
    | `Eq_sf of sf_t * sf_t
    | `Inclusion of s_t * s_t
    | `MemberShip of o_t * s_t
    | `Relation of ident * (o_t*basesort) list] 

type fol_no_card =   
    [ `Atom of sort * atom_no_card
    | `Negation of fol_no_card
    | `Conjunction of fol_no_card list
    | `Disjunction of fol_no_card list
    | `Implication of fol_no_card*fol_no_card 
    | `Equivalence of fol_no_card*fol_no_card
    | `Exists of (ident*basesort) list * fol_no_card
    | boool
    | `Forall of (ident*basesort) list * fol_no_card
    ]

let rewrite_card_atom : (sort*atom_t) -> fol_no_card = function
  | (`Set s), `CardConstr (set, k) -> 
      let variables : [`Vo of ident] list = generate_finite_set k in
      let names : (string * basesort) list = List.map (function `Vo x -> x, s) variables in
      let finite : s_t =  `FiniteSet (variables :> o_t list) in
      let a = (`Atom ((`Set s), (`Inclusion (set, finite) :> atom_no_card)) :> fol_no_card) in
	`Exists ( names, a)
  | s, `CardConstr (set, k) -> printf "hmmm. funny.\n"; flush stdout; assert false

  | s, (#atom_no_card as a) -> `Atom (s, a)
      
let rec rewrite_card_constraints  : fol_form_t -> fol_no_card = function 
  | `Atom a -> rewrite_card_atom a
  | `Negation f -> `Negation (rewrite_card_constraints f)
  | `Conjunction fs -> `Conjunction (ListLabels.map ~f:rewrite_card_constraints fs)
  | `Disjunction fs -> `Disjunction (ListLabels.map ~f:rewrite_card_constraints fs)
  | `Implication (f1,f2) -> `Implication (rewrite_card_constraints f1, rewrite_card_constraints f2)
  | `Equivalence (f1,f2) -> `Equivalence (rewrite_card_constraints f1, rewrite_card_constraints f2)
  | `Exists (vars,f) -> `Exists (vars, rewrite_card_constraints f)
  | `Forall (vars,f) -> `Forall (vars, rewrite_card_constraints f)
  | #boool as b -> b


type atom_no_seteq =    
    [ `Eq_o of o_t* o_t
    | `Eq_of of of_t * of_t
    | `Eq_sf of sf_t * sf_t
    | `MemberShip of o_t * s_t
    | `Relation of ident * (o_t*basesort) list
    ]
      
type fol_no_seteq =   
    [ `Atom of basesort * atom_no_seteq
    | `Negation of fol_no_seteq
    | `Conjunction of fol_no_seteq list
    | `Disjunction of fol_no_seteq list
    | `Implication of fol_no_seteq*fol_no_seteq 
    | `Equivalence of fol_no_seteq*fol_no_seteq
    | `Exists of (ident*basesort) list * fol_no_seteq
    | `Forall of (ident*basesort) list * fol_no_seteq
    | boool ]

(** get rid of fieldwrites, field equalities, set equalities and set inclusion *)
let rec  rewrite_seteq_atom : sort * atom_no_card -> fol_no_seteq = function
  | `Set s, `Inclusion (s1, s2) ->
      let z = fresh_ident "z_setinc" in
	`Forall ([z,s], `Implication (`Atom (s, `MemberShip (`Vo z, s1)) , `Atom (s, `MemberShip (`Vo z, s2))))
	  
  | `Set s, `Eq_s (s1, s2)  -> `Conjunction [rewrite_seteq_atom  (`Set s, `Inclusion (s1, s2)); rewrite_seteq_atom (`Set s, `Inclusion (s2, s1))] ;  
  | #basesort as s, (#atom_no_seteq as a) -> `Atom (s, a)
  | `Set _, _ -> failwith "set with a base sort ???!??"
  | #basesort, `Inclusion(_,_)
  | #basesort, `Eq_s(_,_) -> failwith "something is broken in rewrite_seteq_atom"
 

let rec rewrite_seteq  : fol_no_card -> fol_no_seteq = function 
  | `Atom a -> rewrite_seteq_atom a
  | `Negation f -> `Negation (rewrite_seteq f)
  | `Conjunction fs -> `Conjunction (ListLabels.map ~f:rewrite_seteq fs)
  | `Disjunction fs -> `Disjunction (ListLabels.map ~f:rewrite_seteq fs)
  | `Implication (f1,f2) -> `Implication (rewrite_seteq f1, rewrite_seteq f2)
  | `Equivalence (f1,f2) -> `Equivalence (rewrite_seteq f1, rewrite_seteq f2)
  | `Exists (vars,f) -> `Exists (vars, rewrite_seteq f)
  | `Forall (vars,f) -> `Forall (vars, rewrite_seteq f)
  | #boool as b -> b


	
type atom_no_setop =   
    [ `Eq_o of o_t * o_t
    | `Eq_of of of_t * of_t
    | `Eq_sf of sf_t * sf_t
    | `MemberShip of o_t * [vs_t | `VsVf of o_t*sf_t]
    | `Relation of ident * (o_t*basesort) list
    ]

type fol_no_setop =   
    [ `Atom of basesort*atom_no_setop
    | `Negation of fol_no_setop
    | `Conjunction of fol_no_setop list
    | `Disjunction of fol_no_setop list
    | `Implication of fol_no_setop*fol_no_setop
    | `Equivalence of fol_no_setop*fol_no_setop
    | `Exists of (ident*basesort) list * fol_no_setop
    | `Forall of (ident*basesort) list * fol_no_setop
    | boool ]

let aux (o:o_t) (s:s_t) : atom_no_seteq = `MemberShip (o, s)

let rec rewrite_setop_atom (s:basesort) : atom_no_seteq -> fol_no_setop = function
  |  (`Relation _ as a) 
  | (`Eq_o _ as a) 
  | (`Eq_of _ as a) 
  | (`Eq_sf _ as a) 
  | (`MemberShip (_, `Vs _) as a) 
  | (`MemberShip (_, `VsVf _) as a) -> `Atom (s,a)
  | `MemberShip (o, `Intersection (s1, s2)) -> `Conjunction (ListLabels.map ~f:(rewrite_setop_atom s) [aux o s1 ; aux o s2])
  | `MemberShip (o, `Union (s1, s2)) -> `Disjunction (ListLabels.map ~f:(rewrite_setop_atom s) [aux o s1 ; aux o s2])
  | `MemberShip (o, `Difference (s1, s2)) -> `Conjunction [rewrite_setop_atom s (aux o s1) ; `Negation (rewrite_setop_atom s (aux o s2))]
  | `MemberShip (o, `FiniteSet []) -> `False
  | `MemberShip (o, `UniversalSet) -> `True
  | `MemberShip (o, `FiniteSet set) -> `Disjunction (ListLabels.map ~f:(fun x -> `Atom (s, `Eq_o (o, x))) set)
  | `MemberShip (o, `Comprehension f) -> rewrite_setop (rewrite_seteq (rewrite_card_constraints (f o)))

and rewrite_setop  : fol_no_seteq -> fol_no_setop = function 
  | `Atom (s,a)  -> rewrite_setop_atom s a
  | `Negation f -> `Negation (rewrite_setop f)
  | `Conjunction fs -> `Conjunction (ListLabels.map ~f:rewrite_setop fs)
  | `Disjunction fs -> `Disjunction (ListLabels.map ~f:rewrite_setop fs)
  | `Implication (f1,f2) -> `Implication (rewrite_setop f1, rewrite_setop f2)
  | `Equivalence (f1,f2) -> `Equivalence (rewrite_setop f1, rewrite_setop f2)
  | `Exists (vars,f) -> `Exists (vars, rewrite_setop f)
  | `Forall (vars,f) -> `Forall (vars, rewrite_setop f)
  | #boool as b -> b

(* if we were translating with only function symbols, we could relax the constraints, by replacing vo_t by o_no_fw in most of the cases... 
   Note : for some reason, this seems to be slower. I don't have an explanation *)
type o_no_fw = [vo_t 
| `Fun of ident*((vo_t*basesort) list) 
| `Tuple_o of (vo_t*basesort) list 
| `VoVf of vo_t*[`Fo of ident ] 
| `ArrayRead of [`ArrayStateVar of ident] * vo_t * vo_t]
type s_no_fw = [vs_t | `VsVf of vo_t*[`Fs of ident ]]
type atom_no_fieldeq =   
    [ `Eq_o of vo_t * o_no_fw
    | `MemberShip of vo_t * s_no_fw
    | `Relation of ident * (vo_t*basesort) list
    ]

(* these are in NNF *)
type fol_no_fieldeq =   
    [ `Atom of basesort * atom_no_fieldeq
    | `Negation of basesort * atom_no_fieldeq
    | `Conjunction of fol_no_fieldeq list
    | `Disjunction of fol_no_fieldeq list
    | `Exists of (ident*basesort) list * fol_no_fieldeq
    | `Forall of (ident*basesort) list * fol_no_fieldeq
    | boool ]


let rec stupid_casting : fol_no_fieldeq -> fol_no_setop = function
  | `Atom (s, a) -> `Atom (s, (a : atom_no_fieldeq :> atom_no_setop))
  | `Negation (s, a) -> `Negation (`Atom (s, (a : atom_no_fieldeq :> atom_no_setop)))
  | `Conjunction fs -> `Conjunction (ListLabels.map ~f:stupid_casting fs)
  | `Disjunction fs -> `Disjunction (ListLabels.map ~f:stupid_casting fs)
  | #boool as b -> b
  | `Forall (vs, f) -> `Forall (vs, stupid_casting f)
  | `Exists (vs, f) -> `Exists (vs, stupid_casting f)


let rec string_of_no_fw : o_no_fw -> string = function
  | `Vo v -> v
  | `Int k -> string_of_int k
  | `Null -> "null"
  | `BeingTrue -> "True"
  | `BeingFalse -> "False"
  | `Fun (f, args) -> sprintf "%s(%s)" f (String.concat "," (ListLabels.map ~f:(fun (v,_) -> string_of_no_fw (v :> o_no_fw)) args))
  | `VoVf(x, `Fo f)-> sprintf "FieldRead(%s,%s)" f (string_of_no_fw (x :> o_no_fw))
  | `Tuple_o args -> sprintf "(%s)" (String.concat "," (ListLabels.map ~f:(fun (v,_) -> string_of_no_fw (v :> o_no_fw)) args))
  | `ArrayRead(`ArrayStateVar s, a, i)-> sprintf "ArrayRead(%s,%s,%s)" s (string_of_no_fw (a :> o_no_fw)) (string_of_no_fw (i :> o_no_fw))
  

let string_of_s : s_no_fw -> string = function
  | `Vs s -> s
  | `VsVf(o, `Fs f) -> sprintf "FieldRead(%s,%s)" f (string_of_no_fw (o :> o_no_fw))

let rec string_of_fol_fw :fol_no_fieldeq -> string = function
  | `True -> "True"
  | `False -> "False"
  | `BoolVar v -> v
  | `NegatedBoolVar v ->  "~ " ^ v
  | `Atom (_, `Eq_o (x,y)) -> sprintf "(%s = %s)" (string_of_no_fw (x :> o_no_fw)) (string_of_no_fw (y :> o_no_fw))
  | `Atom (_,`MemberShip (x,y)) -> sprintf "(%s : %s)" (string_of_no_fw (x :> o_no_fw)) (string_of_s y)
  | `Atom (_,`Relation (f, args)) -> sprintf "%s(%s)" f (String.concat "," (ListLabels.map ~f:(fun (v,_) -> string_of_no_fw (v :> o_no_fw)) args))
  | `Negation (s, a) -> "~ " ^ (string_of_fol_fw (`Atom (s,a)))
  | `Conjunction l -> "and(" ^ String.concat ", " (ListLabels.map ~f:string_of_fol_fw l) ^ ")"
  | `Disjunction l -> "or(" ^ String.concat ", " (ListLabels.map ~f:string_of_fol_fw l) ^ ")"
  | `Exists (vs, f) -> sprintf "EX %s. %s" (String.concat " " (ListLabels.map ~f:fst vs)) (string_of_fol_fw f)
  | `Forall (vs, f) -> sprintf "All %s. %s" (String.concat " " (ListLabels.map ~f:fst vs)) (string_of_fol_fw f)


 (** Ok. This is a little tricky. Basically, the purpose of this function is to flatten a list of o_t objects, and turn it to a list of vo_t object variables (NEW : with sorts), with
     associated equalities. Since quantified fresh variables may be introduced, this depend on the polarity (mode) of the occurence.
     The object list we want to flatten is originating from some atom A[x1;x2;...;xn]. This Atom may then appear under the quantifiers. This is achieved by the callback.
     The function takes the list [x1;x2;...;xn] as parameter, and a callback functions which will will map the new list [x1'; x2'; ...; xn'] of flattened objects to the new atom A'.*)

  let rec check_obj_list (args:(o_t*basesort) list) ~(callback:(vo_t*basesort) list->fol_no_fieldeq) ~(mode:unnesting_mode) : fol_no_fieldeq = 
    let check_args (o:o_t*basesort) ((eqs, handled):(((ident*basesort)*o_t) list)*((vo_t*basesort) list)) = 
      match o with
      | (#vo_t as v, s) -> (eqs, (v,s)::handled)
      | (_, `Tuple _) -> failwith "tuples cannot yet be passed as arguments to functionsa or predicates"
      | (o, s) -> 
	  let v = fresh_ident "fun_flat" in
	  (((v, s), o)::eqs, (`Vo v, s)::handled)
    in
    
    let eqs, args' = ListLabels.fold_right ~f:check_args ~init:([],[]) args in
    let main_atom = callback args' in
    match eqs with
    | [] -> main_atom
    | eqs -> 
	let vars, _ = List.split eqs in
	match mode with
	| Existential ->
	let eqs_args : fol_no_fieldeq list = ListLabels.map ~f:(fun ((v,s),o) -> rewrite_fieldWrite_atom ~mode ~s (`Eq_o (`Vo v, o))) eqs in
	    `Exists (vars, `Conjunction (main_atom :: eqs_args))
	| Universal ->
	    let eqs_args : fol_no_fieldeq list = ListLabels.map ~f:(fun ((v,s),o) -> rewrite_fieldWrite_atom ~mode:(switch_mode mode) ~s (`Eq_o (`Vo v, o))) eqs in
	    let step1 : fol_no_setop list = ListLabels.map ~f:stupid_casting eqs_args in
	    let step2 : fol_no_setop = stupid_casting main_atom in
	    let f : fol_no_setop = `Forall (vars, `Implication (`Conjunction step1, step2)) in
	    rewrite_fieldeq ~mode f
     
	      
 and generate_binding ~(var:ident) ~(eq : atom_no_setop) ~(mode:unnesting_mode) ~(s:basesort) (f:fol_no_setop) : fol_no_fieldeq =
  match mode with
     | Existential -> `Exists ([var,s], rewrite_fieldeq ~mode (`Conjunction [`Atom (s,eq); f]))
     | Universal -> let tmp = `Atom (s,eq) in
	 `Forall ([var,s], rewrite_fieldeq ~mode (`Implication (tmp, f)))
	   
 and rewrite_fieldWrite_atom ~(s:basesort) (f:atom_no_setop) ~(mode:unnesting_mode) : fol_no_fieldeq =
   match f with
       (* equality between object-valued fields *)
     | `Eq_of (`FieldWrite_o (f2,o1,o2), `Fo vf1)
     | `Eq_of (`Fo vf1, `FieldWrite_o (f2,o1,o2)) -> 
	 let x = fresh_ident "x_ofeq" and y = fresh_ident "y_ofeq" in
	   `Forall ([(x,`O); (y,s)], rewrite_fieldeq ~mode (`Equivalence (
						     `Atom (s, `Eq_o (`Vo y, `VoVf (`Vo x, `Fo vf1))),
						     `Disjunction [`Conjunction [`Atom (`O, `Eq_o (`Vo x, o1)); `Atom (s, `Eq_o (`Vo y, o2))]; 
								   `Conjunction [`Negation (`Atom (`O, `Eq_o (`Vo x, o1))) ; `Atom (s, `Eq_o (`Vo y, `VoVf (o2, f2))) ]])
						  ))

     (* FWrite1 = FWrite2 ---> unnesting with a field var. Note that the field vars cannot depend on the quantified objects above. 
	Thus, we don't need to output a quantifier. *)
     | `Eq_of (`FieldWrite_o f1, `FieldWrite_o f2) ->
	 let t = fresh_ident "x_ofeq" in
	   rewrite_fieldeq ~mode (`Conjunction [ `Atom (s, `Eq_of (`FieldWrite_o f1, `Fo t)) ;
						 `Atom (s, `Eq_of (`Fo t, `FieldWrite_o f2)) 
					       ])
     | `Eq_of (`Fo vf1, `Fo f2) -> 
	 let x = fresh_ident "x_ofeq" in
	   `Forall ([x, `O], rewrite_fieldWrite_atom ~s ~mode (`Eq_o (`VoVf (`Vo x, `Fo f2), `VoVf (`Vo x, `Fo f2))))
	     
     (* equality between set-valued fields. TRICK : the set expression hidden in the fieldwrite has not been rewritten *)
     | `Eq_sf (`FieldWrite_s (f2,o,set), `Fs vf1)
     | `Eq_sf (`Fs vf1, `FieldWrite_s (f2,o,set)) -> 
	 let x = fresh_ident "x_sfeq" and y = fresh_ident "y_sfeq" in
	   `Forall ([(x,`O); (y,s)],  rewrite_fieldeq ~mode ( `Equivalence (
							       `Atom (s, `MemberShip (`Vo y, `VsVf (`Vo x, `Fs vf1))),
							       `Disjunction [`Conjunction [`Atom (`O, `Eq_o (`Vo x, o)); rewrite_setop_atom s (`MemberShip (`Vo y, set))]; 
									     `Conjunction [`Negation (`Atom (`O, `Eq_o (`Vo x, o))); `Atom (s, `MemberShip (`Vo y, `VsVf (`Vo x, f2)))]])
							   ))
	     
     (* FWrite1 = FWrite2 ---> unnesting with a field var. Note that the field vars cannot depend on the quantified objects above. 
	Thus, we don't need to output a quantifier. *)
     | `Eq_sf (`FieldWrite_s f1, `FieldWrite_s f2) -> 
	 let t = fresh_ident "x_sfeq" in
	   rewrite_fieldeq ~mode (`Conjunction [ `Atom (s, `Eq_sf (`Fs t, `FieldWrite_s f1)) ;
						 `Atom (s, `Eq_sf (`Fs t, `FieldWrite_s f2))] )
     | `Eq_sf (`Fs vf1, `Fs vf2) -> 
	 let x = fresh_ident "x_sfeq" and y = fresh_ident "y_sfeq" in
	   `Forall ([(x,`O); (y,s)],  rewrite_fieldeq ~mode ( `Equivalence (`Atom (s, `MemberShip (`Vo y, `VsVf (`Vo x, `Fs vf1))),
									    `Atom (s, `MemberShip (`Vo y, `VsVf (`Vo x, `Fs vf2)))))
		   )

     (****************** Everything above this line should die *****************)

     (* these are the final cases : Vo=Vo, Vo=Vo.Vfo, Vo \in Vs, Vo \in Vo.Vfs, vo=f ( [Vo|Vo.Vfo]+ ) *)
      | (`Eq_o (#vo_t, #vo_t) as a) 
      | (`Eq_o (#vo_t, `VoVf (#vo_t, #ofv_t)) as a)
      | (`MemberShip (#vo_t, `VsVf (#vo_t, #sfv_t)) as a) 
      | (`Eq_o (#vo_t, `ArrayRead (`ArrayStateVar _, #vo_t, #vo_t )) as a) 
      | (`MemberShip (#vo_t, #vs_t) as a) -> `Atom (s, a)

      (* some forbidden use of tuples *)
      | `Eq_o (_, `ArrayRead (_, `Tuple_o _ , _ )) 
      | `Eq_o (_, `ArrayRead (_, _, `Tuple_o _ )) 
      | `Eq_o (_, `VoVf (`Tuple_o _ , _)) 
      | `Eq_o (_, `ArrayRead (`ArrayWrite (_, _, _, `Tuple_o _), _, _ ))
      | `MemberShip (_, `VsVf (`Tuple_o _ , _)) -> failwith "a tuple stand for an object"

      (* done with the terminating cases : symetry of equality to be in a normalize configuration. cannot loop because if l were a variable, it would be caught by
	 the final cases *)
      | `Eq_o (l, (#vo_t as r)) -> rewrite_fieldWrite_atom ~s ~mode (`Eq_o (r, l))

      (* a special one is the handling of functions*)
      | `Eq_o (#vo_t as v, `Fun (name, args)) -> check_obj_list ~mode ~callback:(fun args' -> `Atom (s, `Eq_o (v, `Fun (name, args')))) args
      | `Eq_o (#vo_t as v, `Tuple_o args) ->  check_obj_list ~mode ~callback:(fun args' -> `Atom (s, `Eq_o (v, `Tuple_o args'))) args

      (* The handling of relations is quite similar *)
      | `Relation (f, args) ->  check_obj_list ~mode ~callback:(fun args' -> `Atom (s, `Relation (f, args'))) args
	     

      (* From now on : unnesting of object variables *)

      (* fieldwrite in object equality *)
      | `Eq_o (#vo_t as o1, `VoVf (o2, `FieldWrite_o (f, (o3), o4))) ->
	  let o2 = (o2 :> o_t) 
	  and o3 = (o3 :> o_t) in
	    rewrite_fieldeq ~mode (`Disjunction [`Conjunction [ `Atom (`O, `Eq_o (o2, o3));  `Atom (s, `Eq_o (o1, o4))] ;
					 	 `Conjunction [ `Negation ( `Atom (`O, `Eq_o (o2, o3))); `Atom (s, `Eq_o (o1, `VoVf (o2, f)))]])
				     
      (* fieldwrite in set membership. TRICK : the set expression hidden in the fieldwrite has not been rewritten *)
      | `MemberShip (#vo_t as o1, `VsVf (o2, `FieldWrite_s (f, o3, set))) ->
	  rewrite_fieldeq ~mode (`Disjunction [`Conjunction [ `Atom (`O, `Eq_o (o2, o3)); rewrite_setop_atom s (`MemberShip (o1, set))] ;
					       `Conjunction [ `Negation (`Atom (`O, `Eq_o (o2, o3))); `Atom (s, `MemberShip (o1, `VsVf (o2, f)))]])
      
      (* handling of arrays. First : flattening of the first argument *)
      | `Eq_o (#vo_t as v, `ArrayRead (`ArrayStateVar v2, (`VoVf _ as array_name), (#o_t as index) ))
      | `Eq_o (#vo_t as v, `ArrayRead (`ArrayStateVar v2, (`Fun _ as array_name), (#o_t as index) )) 
      | `Eq_o (#vo_t as v, `ArrayRead (`ArrayStateVar v2, (`ArrayRead _ as array_name), (#o_t as index))) ->
	  let var = fresh_ident "t_eqof" in
	    generate_binding ~s:(`O) ~var ~mode ~eq:(`Eq_o (`Vo var, array_name)) (`Atom (s,`Eq_o (v, `ArrayRead (`ArrayStateVar v2, `Vo var, index))))
	  
      (* handling of arrays. First : flattening of the second argument *)
      | `Eq_o (#vo_t as v, `ArrayRead (`ArrayStateVar v2, (#vo_t as array_name), (`VoVf _ as index) ))
      | `Eq_o (#vo_t as v, `ArrayRead (`ArrayStateVar v2, (#vo_t as array_name), (`Fun _ as index) ))
      | `Eq_o (#vo_t as v, `ArrayRead (`ArrayStateVar v2, (#vo_t as array_name), (`ArrayRead _ as index))) ->
	  let var = fresh_ident "t_eqof" in
	    generate_binding ~mode ~var ~s:(`I) ~eq:(`Eq_o (`Vo var, index)) (`Atom (s, `Eq_o (v, `ArrayRead (`ArrayStateVar v2, array_name, `Vo var) )))
	  
      (* handling of arrays. Nested ReadWrites *)
      | `Eq_o (#vo_t as v, `ArrayRead (`ArrayWrite (global_state, name2, index2, content2), (#o_t as array_name1), (#o_t as index1) )) ->
	  rewrite_fieldeq ~mode (`Disjunction [`Conjunction [`Atom (`O, `Eq_o (array_name1, name2)) ; `Atom (`I, `Eq_o (index1, index2)) ; `Atom (s, `Eq_o (v, content2))] ;
					       `Conjunction [`Negation (`Conjunction [`Atom (`O, `Eq_o (array_name1, name2)) ; `Atom (`I, `Eq_o (index1, index2))]) ; 
							     `Atom (s, `Eq_o (v, `ArrayRead (global_state, array_name1, index1)))]
						])

      (* very limited support for tuples here. avoids introducing n variables for (x1,...,xn)=(y1,...,yn) *)
      | `Eq_o (`Tuple_o t1, `Tuple_o t2) -> `Conjunction (ListLabels.map2 ~f:(fun (o1,s) (o2,_) -> rewrite_fieldWrite_atom ~mode ~s (`Eq_o(o1, o2))) t1 t2)
      | `MemberShip (`Tuple_o t, `Vs set) -> rewrite_fieldWrite_atom ~mode ~s (`Relation (set, t))
      | `MemberShip (`Tuple_o t, `VsVf(#vo_t as o, `Fs f)) -> rewrite_fieldWrite_atom ~mode ~s (`Relation (f, (o, `O)::t))

      (* o1.f = # : unnest o1.f (explanation : with the above symmetry rule, this means than # is not a variable) *)
      | `Eq_o (`ArrayRead _ as a, b) 
      | `Eq_o (`Fun _ as a, b) 
      | `Eq_o (`Tuple_o _ as a, b) 
      | `Eq_o (`VoVf _ as a, b)  ->
	  let var = fresh_ident "t_eqof" in
	    generate_binding ~mode ~s ~var ~eq:(`Eq_o (`Vo var, a)) (`Atom (s,`Eq_o (`Vo var, b)))

      (* Vo = o1.o2.f ... We know that f is not a fieldwrite, and that o2 is not a field var *)
      | `Eq_o (#vo_t as o1, `VoVf (`VoVf _ as o2, (`Fo _ as f))) 
      | `Eq_o (#vo_t as o1, `VoVf (`ArrayRead _ as o2, (`Fo _ as f))) 
      | `Eq_o (#vo_t as o1, `VoVf (`Fun _ as o2, (`Fo _ as f))) ->
	  let var = fresh_ident "t_eqof" in
	   generate_binding ~s:(`O) ~mode ~var ~eq:(`Eq_o (`Vo var, o2)) (`Atom (s, `Eq_o (o1, `VoVf (`Vo var, f)))) 
	      
      (* Vo \in (o2.o3).f ... We must unnest o2.o3 *)
      | `MemberShip (#vo_t as o1, `VsVf ((`Fun _) as o2 , fs)) 
      | `MemberShip (#vo_t as o1, `VsVf ((`ArrayRead _) as o2 , fs)) 
      | `MemberShip (#vo_t as o1, `VsVf ((`VoVf _) as o2 , fs)) ->
	  let var = fresh_ident "t_ms2" in
	    generate_binding ~s:(`O) ~mode ~var ~eq:(`Eq_o (`Vo var, o2)) (`Atom (s, `MemberShip (o1, `VsVf (`Vo var, fs))))

      (* o.f \in s ... We must unnest o.f *)
      | `MemberShip (`Fun _ as o1, set)
      | `MemberShip (`ArrayRead _ as o1, set)
      | `MemberShip (`VoVf _ as o1, set) 
      | `MemberShip (`Tuple_o _ as o1, set) ->
	  let var = fresh_ident "t_ms1" in
	    generate_binding ~s ~mode ~var ~eq:(`Eq_o (`Vo var, o1)) (`Atom (s, `MemberShip (`Vo var, set)))
	      
     
 and fun_conversion (l:(o_t*basesort) list) : (vo_t*basesort) list = 
   ListLabels.map ~f:(function | (#vo_t as a, s) -> a,s | _ -> failwith "wasn't possible") l
     
 and atom_filter ~(s:basesort) ~mode (a:atom_no_setop) : fol_no_fieldeq = match a with
   | (`Eq_o (#vo_t, #vo_t) as a)
   | (`Eq_o (#vo_t, `ArrayRead (`ArrayStateVar _, #vo_t, #vo_t)) as a)
   | (`Eq_o (#vo_t, `VoVf (#vo_t, #ofv_t)) as a)
   | (`MemberShip (#vo_t, `VsVf (#vo_t, #sfv_t)) as a)
   | (`MemberShip (#vo_t, #vs_t) as a) -> `Atom (s, a)
       
   | (`Eq_o (#vo_t as v, (`Fun (f, args))) as a) -> 
       (try 
	  let l = fun_conversion args in
	  `Atom (s, (`Eq_o(v, `Fun (f, l)) :> atom_no_fieldeq))
	with Failure _ -> ((rewrite_fieldWrite_atom ~s ~mode (a:>atom_no_setop)) : fol_no_fieldeq)
       )
	 
   | (`Eq_o (#vo_t as v, (`Tuple_o args)) as a) -> 
       (try 
	  let l = fun_conversion args in
	  `Atom (s, (`Eq_o(v, `Tuple_o l) :> atom_no_fieldeq))
	with Failure _ -> ((rewrite_fieldWrite_atom ~s ~mode (a:>atom_no_setop)) : fol_no_fieldeq)
       )

   | `Relation (f, args) as a -> 
       (try (`Atom (s, `Relation (f, fun_conversion args)))
	with Failure _ -> rewrite_fieldWrite_atom ~s ~mode (a : atom_no_setop))

   | a -> rewrite_fieldWrite_atom ~s ~mode (a :> atom_no_setop)

 and atom_filter_negated ~(s:basesort) ~mode (a:atom_no_setop) : fol_no_fieldeq = 
   try match a with
     | (`Eq_o (#vo_t, #vo_t) as a)
     | (`Eq_o (#vo_t, `ArrayRead (`ArrayStateVar _, #vo_t, #vo_t)) as a)
     | (`Eq_o (#vo_t, `VoVf (#vo_t, #ofv_t)) as a)
     | (`MemberShip (#vo_t, `VsVf (#vo_t, #sfv_t)) as a)
     | (`MemberShip (#vo_t, #vs_t) as a) -> `Negation (s, a)
	 
     | `Eq_o (#vo_t as v, (`Fun (f, args))) -> 
	 let l = fun_conversion args in
	 `Negation (s, (`Eq_o(v, `Fun (f, l)) :> atom_no_fieldeq))
	 
     | `Eq_o (#vo_t as v, (`Tuple_o args)) -> 
	 let l = fun_conversion args in
	   `Negation (s, (`Eq_o(v, `Tuple_o l) :> atom_no_fieldeq))
       

   | `Relation (f, args)  -> `Negation (s, `Relation (f, fun_conversion args))
   | a -> failwith "ok" 
with
  | Failure _ -> rewrite_fieldeq ~mode (`Negation (stupid_casting (rewrite_fieldWrite_atom ~s ~mode:(switch_mode mode) a))) 


 and rewrite_fieldeq ~(mode:unnesting_mode) : fol_no_setop -> fol_no_fieldeq = function
     (* final cases *)
   | `Atom (s, a) -> (*let r = atom_filter ~s ~mode a in printf "\n\n%s\n" (string_of_fol_fw r); r*)
       atom_filter ~s ~mode a 

   | `Negation (`Atom (s, a)) -> atom_filter_negated ~s ~mode a
       
  | `Negation (#boool as b) -> (switch_bool b :> fol_no_fieldeq)
  | `Negation (`Negation f) -> rewrite_fieldeq ~mode f
  | `Negation (`Forall (v,f)) -> `Exists (v, rewrite_fieldeq ~mode:Existential (`Negation f))
  | `Negation (`Exists (v,f)) -> `Forall (v, rewrite_fieldeq ~mode:Universal (`Negation f))
  | `Negation (`Conjunction fs) -> `Disjunction (ListLabels.map ~f:(fun x -> rewrite_fieldeq ~mode (`Negation x)) fs)
  | `Negation (`Disjunction fs) -> `Conjunction (ListLabels.map ~f:(fun x -> rewrite_fieldeq ~mode (`Negation x)) fs)
  | `Negation (`Implication (f1,f2)) -> rewrite_fieldeq ~mode (`Conjunction [f1; `Negation f2])
  | `Negation (`Equivalence (f1,f2)) -> rewrite_fieldeq ~mode (`Negation (`Conjunction [`Implication (f1,f2); `Implication (f2,f1)]))
      
  | `Conjunction fs -> `Conjunction (ListLabels.map ~f:(rewrite_fieldeq ~mode) fs)
  | `Disjunction fs -> `Disjunction (ListLabels.map ~f:(rewrite_fieldeq ~mode) fs)
  | `Implication (f1,f2) -> rewrite_fieldeq ~mode (`Disjunction [`Negation f1; f2])
  | `Equivalence (f1,f2) -> rewrite_fieldeq ~mode (`Conjunction [`Implication (f1,f2); `Implication (f2,f1)])
  | `Exists (vars,f) -> `Exists (vars, rewrite_fieldeq f ~mode:Existential  )
  | `Forall (vars,f) -> `Forall (vars, rewrite_fieldeq f ~mode:Universal  )
  | #boool as b -> b
      

(** {6 De-tupling } *)

type o_no_tuple = [vo_t | `Fun of ident*((vo_t*basesort) list) | `VoVf of vo_t*[`Fo of ident ] | `ArrayRead of [`ArrayStateVar of ident] * vo_t * vo_t]
type atom_no_tuple =   
    [ `Eq_o of vo_t * o_no_tuple
    | `MemberShip of vo_t * s_no_fw
    | `Relation of ident * (vo_t*basesort) list
    ]

(* these are NOT in NNF *)
type fol_no_tuple =   
    [ `Atom of basesort * atom_no_tuple
    | `Negation of fol_no_tuple
    | `Conjunction of fol_no_tuple list
    | `Disjunction of fol_no_tuple list
    | `Exists of (ident*basesort) list * fol_no_tuple
    | `Forall of (ident*basesort) list * fol_no_tuple
    | boool ]


let rec expand_var_tuple ?(n=0) ~v = function
  | [] -> []
  | s::tail -> (sprintf "%s_%d" v n, s)::expand_var_tuple ~v ~n:(n+1) tail


let atom_detupling ~s : atom_no_fieldeq -> fol_no_tuple = function
  | `Eq_o (`Vo v, `Tuple_o args) -> 
      let _, sorts = List.split args in
      let vs : (ident*basesort) list = expand_var_tuple ~v sorts in
	`Conjunction (ListLabels.map2 ~f:(fun (v1, s) (v2, _) -> `Atom (s, (`Eq_o (`Vo v1, v2) :> atom_no_tuple) )) vs args)

  | (`Eq_o (`Vo x, `Vo y) as a) -> 
      (match s with 
	 | `Tuple sorts ->
	     let vs_x : (ident*basesort) list = expand_var_tuple ~v:x sorts in
	     let vs_y : (ident*basesort) list = expand_var_tuple ~v:y sorts in
	       `Conjunction (ListLabels.map2 ~f:(fun (v1, s) (v2, _) -> `Atom (s, `Eq_o (`Vo v1, `Vo v2))) vs_x vs_y)
	 | _ -> `Atom(s, a)
      )

  | (`Eq_o (_, (#o_no_tuple))) as a -> `Atom (s, a)
  | (`Eq_o (#vo_t, `Tuple_o _)) -> failwith "incorrect usage of tuple"

  | (`MemberShip (`Vo v, `Vs var)) as a ->
      (match s with
	 | `Tuple sorts -> 
	     let vs : (ident*basesort) list = expand_var_tuple ~v sorts in
	     let vs' : (vo_t*basesort) list = ListLabels.map ~f:(fun (o,s) -> `Vo o, s) vs in
	       `Atom (`B, `Relation (var, vs'))
	 | _ -> `Atom (s, a)
      )

  | (`MemberShip (`Vo v, `VsVf(o, `Fs set))) as a ->
      (match s with
	 | `Tuple sorts -> 
	     let vs : (ident*basesort) list = expand_var_tuple ~v sorts in
	     let vs' : (vo_t*basesort) list = ListLabels.map ~f:(fun (o,s) -> `Vo o, s) vs in
	       `Atom (`B, `Relation (set, (o, `O)::vs'))
	 | _ -> `Atom (s, a)
      )

  | (`MemberShip (_, _)) as a -> `Atom (s, a)

  | `Relation _ as a -> `Atom (s, a)

let foo : (ident*basesort) -> (ident*basesort) list = function
  | v, `Tuple sorts -> expand_var_tuple ~v sorts
  | v,s -> [v,s]

let rec fol_detupling : fol_no_fieldeq -> fol_no_tuple = function
  | `Atom (s,a) -> atom_detupling ~s a
  | `Negation (s,a) -> `Negation (atom_detupling ~s a)
  | `Conjunction fs -> `Conjunction (ListLabels.map ~f:fol_detupling fs)
  | `Disjunction fs -> `Disjunction (ListLabels.map ~f:fol_detupling fs)
  | `Exists (vars,f) -> 
      let tmp = ListLabels.map ~f:foo vars in
	`Exists (List.concat tmp, fol_detupling f)
  | `Forall (vars,f) -> 
      let tmp = ListLabels.map ~f:foo vars in
	`Forall (List.concat tmp, fol_detupling f)
  | (#boool as b) -> b




module OrderedForm = struct
  type t = fol_form_t
  let compare = Pervasives.compare
end

module OrderedInt = struct
  type t = int
  let compare = Pervasives.compare
end

module FormSet = Set.Make(OrderedForm)
module IntSet = Set.Make(OrderedInt)

let obj_field_ax ~(s:basesort) (f:string) : fol_form_t =
  let x = fresh_ident "x_obj_ax"
  and y = fresh_ident "y_obj_ax"
  and z = fresh_ident "z_obj_ax" in
  let s' = sort s in
    `Conjunction [
      `Forall ([x,s ;y,s ;z,s ], `Implication (`Conjunction [`Atom (s', `Eq_o (`Vo y, `VoVf (`Vo x, `Fo f))); `Atom (s', `Eq_o (`Vo z, `VoVf (`Vo x, `Fo f)))], `Atom (s', `Eq_o (`Vo y, `Vo z)))) ;
      `Forall ([x,s ], `Exists ([y,s ], `Atom (s', `Eq_o (`Vo y, `VoVf (`Vo x, `Fo f)))))
    ]

let sort_set_ax ~(s:basesort) (f:string) : fol_form_t =
  let s' = sort s in (* F###ing type system *)
  let x = fresh_ident "x_set_sort" in
    `Forall ([x,s], `Implication(`Atom (s', `MemberShip (`Vo x, `Vs f)), `Atom (s', `MemberShip (`Vo x, `Vs (sort_set_name s)))))
  
let sort_set_field_ax ~(s:basesort) (f:string) : fol_form_t =
  let s' = sort s in (* F###ing type system *)
  let x = fresh_ident "x_set_sort" and y = fresh_ident "y_set_sort" in
    `Forall ([(x,s); (y, `O)], `Implication(`Atom (s', `MemberShip (`Vo x, `VsVf (`Vo y, `Fs f))), `Atom (s', `MemberShip (`Vo x, `Vs (sort_set_name s)))))


(** scan the formula and look for fields deferences : we must state axioms constraining fields to take only ONE value for a given object. 
    also constraint the elements in a set to be of a given sort.*)
let rec find_axioms ~(f:fol_no_fieldeq) (ax:FormSet.t) : FormSet.t =
  match f with
     | `Atom (s, `Eq_o (#vo_t, `VoVf (#vo_t, `Fo f))) -> FormSet.add (obj_field_ax ~s f) ax

     | `Atom (s, `MemberShip (#vo_t, `Vs set)) -> FormSet.add (sort_set_ax ~s set) ax
     | `Atom (s, `MemberShip (#vo_t, `VsVf (#vo_t, `Fs f))) -> FormSet.add (sort_set_field_ax ~s f) ax

     | `Conjunction fs 
     | `Disjunction fs -> ListLabels.fold_left ~f:(fun ax f -> find_axioms ~f ax) ~init:ax fs

     | `Negation (s,a) -> find_axioms ~f:(`Atom (s,a)) ax
     | `Exists (_,f)
     | `Forall (_,f) -> find_axioms ~f:f ax
     | _ -> ax




let fol_of_unnested (f:fol_no_tuple) : fol_formula = 
  let name bound : vo_t*basesort -> term = function
    | `Null, _ -> set_sort "null" `O ; `O, `Constant "null"
    | `Int k, _ -> `I, `Int k
    | `Vo v, s -> s, if StringSet.mem v bound then `Variable v else (set_sort v s ; `Constant v )
    | `BeingFalse, _
    | `BeingTrue, _ -> failwith "I don't like the truth"

  in
    (* is automatic eta-reduction available ? *)
  let set_of_list l = ListLabels.fold_right ~f:StringSet.add ~init:StringSet.empty l 
  in
  let rec term_conversion bound : o_no_tuple*basesort -> term = function
    | (#vo_t as v), s -> name bound (v,s)
    | `VoVf (#vo_t as y, `Fo f), s -> s, `Function (f, [name bound (y, `O)])
    | `ArrayRead (`ArrayStateVar s, a, i), so -> term_conversion bound ( `Fun (s, ([a, `O; i, `I] )), so)
    | `Fun (f, args), s -> s, `Function (f, ListLabels.map ~f:(name bound) args)
  in

  let rec foo ~(bound : StringSet.t) (f : fol_no_tuple) : fol_formula = 
    match (!translation_mode, f) with
      | m, `Atom (s,a) -> 
	  (match m, a with

	    (* handling of boolean values and of user-defined relations *)
	    | _, `Eq_o (`BeingTrue, `VoVf (x, `Fo f)) -> `Predicate (f, [name bound (x,`O)])
	    | _, `Eq_o (`BeingFalse, `VoVf (x, `Fo f)) -> `Negation (`Predicate (f, [name bound (x,`O)]))

	    | _, `Eq_o (`BeingTrue, `Vo x) -> `Predicate (x, [])
	    | _, `Eq_o (`Vo x, `BeingTrue) -> `Predicate (x, [])

	    | _, `Eq_o (`BeingFalse, `Vo x) -> `Negation (`Predicate (x, []))
	    | _, `Eq_o (`Vo x, `BeingFalse) -> `Negation (`Predicate (x, []))

	    | _, `Eq_o (`BeingFalse, `BeingFalse) -> `True
	    | _, `Eq_o (`BeingTrue, `BeingTrue) -> `True

	    | _, `Eq_o (`BeingFalse, `BeingTrue) -> `False
	    | _, `Eq_o (`BeingTrue, `BeingFalse) -> `False

	    | _, `Relation (f, args) -> `Predicate (f, ListLabels.map ~f:(name bound) args)

	    | _, `Eq_o (`BeingFalse, t) -> failwith "no"
	    | _, `Eq_o (t, `BeingFalse) -> failwith "no"

	    (* equality between non-tuples simple terms *)
	    | _, `Eq_o (#vo_t as x, (#vo_t as y)) -> `Equality (name bound (x,s), name bound (y,s))
	
	
  
	    (* predicate version --- OUTDATED ! DO NOT USE !*)
	    | `Predicates, _ -> failwith "this code (for predicate translation) is not up to date. Do not use it. I kept it because I'm too lazy to remove it."
	   (* | `Predicates, `Eq_o (x, `VoVf (y, `Fo f)) -> `Predicate (f, [name bound (y,s) ; name bound (x,s)]) 
	    | `Predicates, `MemberShip (x, `Vs set) -> set_sort_set set s; `Predicate (set, [name bound (x,s)])
	    | `Predicates, `MemberShip (x, `VsVf (y, `Fs f)) -> set_sort_setf f s ;`Predicate (f, [name bound (y,s) ; name bound (x,s)])
	    | `Predicates, `Eq_o (x, `ArrayRead (`ArrayStateVar st, a, i)) -> `Predicate (st, ListLabels.map ~f:(name bound )[(a, `O); (i, `I); (x, s)]) 
	    | `Predicates, `Eq_o (x, (`Fun _ as o)) -> `Equality (name bound (x,s), term_conversion bound (o,s))  *)
		


	    (* function symbol version *)
	    | `Function_symbols, `Eq_o (x, o) -> `Equality (name bound (x,s), term_conversion bound (o,s))
	    | `Function_symbols, `MemberShip (x, `Vs set) -> set_sort_set set s ;`Predicate (set, [name bound (x,s)])
	    | `Function_symbols, `MemberShip (x, `VsVf (y, `Fs f)) ->  set_sort_setf f s ;`Predicate (f, [name bound (y,s) ; name bound (x,s)])
	  )
	    
      | _, `Negation f -> `Negation (foo ~bound f)
      | _, `Conjunction fs -> `Conjunction (ListLabels.map ~f:(foo ~bound) fs)
      | _, `Disjunction fs -> `Disjunction (ListLabels.map ~f:(foo ~bound) fs)
      | _, `Exists (vars,f) -> `Exists (vars, foo ~bound:(StringSet.union bound (set_of_list (fst (List.split vars)))) f)
      | _, `Forall (vars,f) -> `Forall (vars, foo ~bound:(StringSet.union bound (set_of_list (fst (List.split vars)))) f)
      | _, (#boool as b) -> b
    in
      foo ~bound:StringSet.empty f
    

(** generates all the comparisons (clique) for the ints in the formula. Also state that the int constants are integers. *)
let int_axioms (is:IntSet.t) : FormSet.t =
  let i = IntSet.elements is in
  let rec foo i : int -> fol_form_t = function
    | i' when i<i' -> (`Conjunction ([`Atom (`B, `Relation ("lteq", [(`Int i, `I); (`Int i', `I)])); 
				     `Negation (`Atom (`I, `Eq_o (`Int i, `Int i')))]) :> fol_form_t)
    | i' when i=i' -> `True
    | i' -> (`Conjunction [`Atom (`B, `Relation ("lteq", [(`Int i', `I); (`Int i, `I)])); 
			   `Negation (`Atom (`I, `Eq_o (`Int i, `Int i')))] :> fol_form_t)
  and bar = function
    | [] -> []
    | i::tail -> (ListLabels.map ~f:(foo i) tail) @ (bar tail)
  in
      


  let clique = ListLabels.fold_right ~f:FormSet.add ~init:FormSet.empty (bar i) in
    ListLabels.iter ~f:(fun k -> set_sort (string_of_int k) `I) i;
    clique

let rec find_ints (i:IntSet.t) (f:form) = 
  match f with
    | Const (IntConst k) -> IntSet.add k i
    | App (h, args) -> ListLabels.fold_left ~f:find_ints ~init:(find_ints i h) args
    | TypedForm (f, _) -> find_ints i f
    | Binder (_, _, f) -> find_ints i f
    | _ -> i

(** some satisfaibility-presrving stupid optimisations *)
let rec peephole_optimisations : fol_formula -> fol_formula = function
  | `Conjunction l -> 
      let l' = List.map peephole_optimisations l in
	if ListLabels.mem (`False) ~set:l' then `False else
	  (match ListLabels.filter ~f:(fun x -> x <>  `True) l' with
	     | [] -> `True
	     | [x] -> x
	     | l -> `Conjunction l
	  )
 | `Disjunction l -> 
      let l' = List.map peephole_optimisations l in
	if ListLabels.mem (`True) ~set:l' then `True else
	  (match ListLabels.filter ~f:(fun x -> x <>  `False) l' with
	     | [] -> `False
	     | [x] -> x
	     | l -> `Disjunction l
	  )
 | `Negation f -> 
     (match peephole_optimisations f with
	| #boool as b -> (switch_bool b :> fol_formula)
	| f -> `Negation f
     )
       
 | `Exists (v, f) ->
     (match peephole_optimisations f with
	| #boool as b -> b
	| f -> `Exists (v, f)
     ) 

 | `Forall (v, f) ->
     (match peephole_optimisations f with
	| #boool as b -> b
	| f -> `Forall (v, f)
     )


 | `Equality (a,b) when a=b -> `True 
 | a -> a

let sort_predicate ~(t:term) : basesort -> fol_formula = function
  | `Unknown -> (match snd t with
		   | `Function (f, _) -> Util.warn ("sort information incomplete for function : " ^ f); `True 
		   | `Variable v -> (* Util.warn ("sort information incomplete for variable : " ^ v); *) `True 
		   | _ -> Util.warn ("sort information incomplete for some term "); `True 
		)
  | #basesort as b -> `Predicate (sort_set_name b, [t])


let rec add_guard : fol_formula -> fol_formula = function
  | `Forall (vs, f) -> `Forall (vs, `Disjunction [`Negation (`Conjunction (ListLabels.map ~f:(fun (v,s) -> sort_predicate ~t:(s, `Variable v) s) vs)); add_guard f])
  | `Exists (vs, f) -> `Exists (vs, `Conjunction ((ListLabels.map ~f:(fun (v,s) -> sort_predicate ~t:(s, `Variable v) s) vs) @ [add_guard f]))
  | `Conjunction fs -> `Conjunction (ListLabels.map ~f:add_guard fs)
  | `Disjunction fs -> `Disjunction (ListLabels.map ~f:add_guard fs)
  | `Negation f -> `Negation (add_guard f)
  | f -> f


(** Remove rtrancl and cardinality constraints from sequent *)
let remove_rtrancl_card (s : sequent) : sequent =
  let non_fol_constants = 
    List.map (fun s -> (mk_var s, 1)) pseudo_constants @
    List.map (fun c -> (Const c, 1)) [Card; Cardeq; Cardleq; Cardgeq]
  in
  let remove_smart = smart_abstract_constructs non_fol_constants in 
  let f = remove_smart (form_of_sequent s) in
  sequent_of_form f 

let big_rewriting (converted : fol_form_t) ~(mode:unnesting_mode) : fol_no_tuple = 
  let no_card = rewrite_card_constraints converted in
  let no_seteq = rewrite_seteq no_card in
  let no_setop = rewrite_setop no_seteq in
  let no_fieldwrite = rewrite_fieldeq no_setop ~mode in
  let no_tuples = fol_detupling no_fieldwrite in
    no_tuples
      

(* may raise an exception (Failure) if the formula is too complex *)
let process_formula (bit:form) ~(options:options_t) ~(env:type_env) ~(mode:unnesting_mode) ~(ax:FormSet.t) : form*fol_formula*FormSet.t = 
  let beta_reduced = FormUtil.unlambda ~keep_comprehensions:false bit in
  let converted = form (FormUtil.negation_normal_form beta_reduced) ~doom_mode:false ~env ~oa:(if mode = Existential then `True else `False) in
  let unnested = big_rewriting ~mode converted in
  let field_axioms = (* match !translation_mode with
    | `Function_symbols -> ax
    | `Predicates -> find_axioms ~f:unnested ax *)
    ax
  in
  let f =  fol_of_unnested unnested in
  let f = if flag_positive ~o:options "Simplifications" then peephole_optimisations f else f in 
  let f = if flag_positive ~o:options "SortGuards" then add_guard f else f in 
    bit, f, field_axioms


(** generates axioms stating the sorts of constants *)
(* TODO : this actually depends on the encoding of fields *)
let const_sort_axioms () : fol_formula list  = 
  (Hashtbl.fold (fun c s ax_set -> (sort_predicate ~t:(s, `Constant c) s)  :: ax_set )
     sort_env [])
  @ 
    (Hashtbl.fold (fun c (s) ax_set -> 
		     let v = fresh_ident "set_sort" in 
		       (`Forall ([v,s], `Disjunction [`Negation (`Predicate (c, [s, `Variable v])); sort_predicate ~t:(s, `Variable v) s])) :: ax_set)
       sort_env_sets [])
  @
    (Hashtbl.fold (fun f (s) ax_set -> 
		     let v = fresh_ident "v_setf_sort" and u = fresh_ident "u_setf_sort" in 
		       (`Forall ([v,s; u,`O], `Disjunction [`Negation (`Predicate (f, [(`O, `Variable u); (s, `Variable v)])); sort_predicate ~t:(s, `Variable  v) s]))::ax_set)
       sort_env_setf [])
    


let debug_fol = ref false

(*                                                     the new axioms --      hypothesis        ---      goal       *)
let fol_of_form ~(options:options_t) (s:sequent) : fol_formula list * (form*fol_formula) list * (form*fol_formula) =
   (* Remove rtrancl_pt and tree  *)
  try
  let mode = StringMap.find "TranslationMode" options in
    translation_mode := (match mode with
			   | "FunctionSymbols" -> `Function_symbols
			   | "Predicates" -> `Predicates 
			   | _ -> failwith "bad translation mode"
			);
    
    (* Clear the sort environnment for constants *)
    Hashtbl.clear sort_env;
    
    (*  Eliminate transitive closure and cardinality constraints *)
    let s_no_transitive_closure =  remove_rtrancl_card  s in

    (* deal with overloaded operators... *)
    let f_disambiguated = (TypeReconstruct.disambiguate (FormUtil.form_of_sequent s_no_transitive_closure)) in

    (* Get types : it is done by Decider.ml *)
    let f1, _ = TypeReconstruct.reconstruct_types [] f_disambiguated in 

    let s_disambiguated = FormUtil.sequent_of_form f1 in

    let (_, _) = s_disambiguated in
    
    let s_no_free_bool_variable = FormUtil.elim_fv_in_seq false ~keep_bool_defs:true s_disambiguated in 
    let s_no_bool_defs = FormUtil.elim_fv_in_seq false ~keep_bool_defs:false s_no_free_bool_variable in 
    let f = form_of_sequent s_no_bool_defs in 
    
(*  let f = form_of_sequent s_no_free_bool_variable in *)

    (* Beta-reduction *)
      
    let f1 = FormUtil.unlambda ~keep_comprehensions:false f in
    
    let f1, env = TermRewrite.rewrite true [TermRewrite.rewrite_lambdas] [] f1 in
    (* get all integer values occuring in the formula *)
    let ints = find_ints IntSet.empty f1 in

    (* Get types : it is done by Decider.ml *)
    let f1, env = TypeReconstruct.reconstruct_types env f1 in 

    (* Replace Ite *)
    let f1 = FormUtil.remove_typedform f1 in
    let f1, env = TermRewrite.rewrite true [TermRewrite.rewrite_fo_ite] env f1 in
    let f1, env = TypeReconstruct.reconstruct_types [] f1 in
    let f1 = TypeReconstruct.disambiguate f1 in

    (* Rewrite set expressions and higher order constructs, abstract cardinality constraints *)
    let f3, _ = TermRewrite.rewrite true [TermRewrite.rewrite_function_eq] env f1 in

    (* Repeat for if-then-else exposed after rewriting function eq *)
    let f3 = FormUtil.remove_typedform f3 in
    let f3, env = TermRewrite.rewrite true [TermRewrite.rewrite_fo_ite] env f3 in
    let f3 = TypeReconstruct.disambiguate f3 in

    (* Get types : it is done by Decider.ml *)
    let f3, env = TypeReconstruct.reconstruct_types [] f3 in 

    let f33 = make_unique_variables f3 in
    
    let hyps, goal = sequent_of_form f33 in  

(*     Printf.printf "\n\n==========================\After pre-processing : %d assumptions\n\n" (List.length hyps); *)
     

     
    let old_goal, new_goal, additional_axioms = process_formula goal ~env ~options ~ax:FormSet.empty ~mode:Universal in 
	 
    let additionnal_axioms, new_hyps = ListLabels.fold_left 
	~f:(fun (axioms, processed_f) f -> 
	  let old_f, new_f, axioms' = process_formula f ~env ~options ~ax:axioms ~mode:Existential in (axioms', (old_f,new_f)::processed_f))
	~init:(additional_axioms, [])
	hyps
    in
    
    let ints_comparison_axioms = int_axioms ints in
    let all_axioms = FormSet.elements (FormSet.union additionnal_axioms ints_comparison_axioms) in
    
    (* OK, we should now process the axioms *)
    let (axioms : fol_formula list) =   (ListLabels.map ~f:(fun a -> fol_of_unnested (big_rewriting ~mode:Existential a)) all_axioms) 

(*     @ (if flag_positive ~o:options "SortGuards" then (const_sort_axioms ()) else []) *)

    in
    (axioms , List.rev new_hyps, (old_goal, new_goal))  
  with
  | e -> printf "exception caught in FolTranslation : %s" (Printexc.to_string e); failwith "no. it's not working"



let awful_hack (s:Form.sequent) ~(options:options_t) : Form.sequent = 
  let axioms, hyps, (_, goal) = fol_of_form ~options s in
  let _, hyps = List.split hyps in
  let s = (ListLabels.map ~f:backward_conversion_f (axioms @ hyps), backward_conversion_f goal) in
    s

(*
let rec split_form : fol_formula -> fol_formula list = function
  | `Conjunction fs -> List.concat (ListLabels.map ~f:split_form fs)
  | `Forall (v, `Conjunction fs) -> split_form (`Conjunction (ListLabels.map ~f:(fun f ->  `Forall (v, f)) fs))
  | `Forall (v, `Forall (v', f)) -> split_form (`Forall (v@v', f))
  | f -> [f]
*)

let rec flatten_and = function
  | [] -> []
  | (`Conjunction l)::tail -> (flatten_and l) @ (flatten_and tail)
  | x::tail -> x :: (flatten_and tail)

let split_form (f : fol_formula) : fol_formula list = 
  let rec foo : fol_formula -> fol_formula = function
    | `Forall (v, `Conjunction fs) -> foo (`Conjunction (ListLabels.map ~f:(fun f ->  `Forall (v, f)) fs))
    | `Exists (v, `Disjunction fs) -> foo (`Disjunction (ListLabels.map ~f:(fun f ->  `Exists (v, f)) fs))
    | `Forall (v, `Forall (v', f)) -> foo (`Forall (v@v', f))
    | `Exists (v, `Exists (v', f)) -> foo (`Exists (v@v', f))
	(* we may want to flatten conjunction/disjunctions *)
    | `Conjunction fs -> `Conjunction (flatten_and (ListLabels.map ~f:foo fs))
    | `Disjunction fs -> 
	let fs' : fol_formula list = ListLabels.map ~f:foo fs in
	let conj, rest = ListLabels.partition ~f:(function | `Conjunction _ -> true | _ -> false) fs' in
	  (match conj with
	    | [] -> `Disjunction fs' (* here ? *)
	    | (`Conjunction gs)::tail -> 
		let f : fol_formula -> fol_formula = fun c -> `Disjunction (c::(tail@rest)) in
		foo (`Conjunction (ListLabels.map ~f gs)) 
	    | _ -> assert false)
	    
    | f -> f
  in
    match foo f with
      | `Conjunction fs -> fs
      | f -> [f]
