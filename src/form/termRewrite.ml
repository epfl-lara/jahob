open Util
open Form
open FormUtil
open PrintForm
open TypeReconstruct

let debug_id = Debug.register_debug_module "TermRewrite"
let debug_lmsg = Debug.debug_lmsg debug_id

(** Variable declaration with optional defining formulas *)
type decl = typedIdent * form option



(** Replace map for common subterm replacements *)
type replaceMap = typedIdent FormHashtbl.t

(** Extended variable declaration for auxiliary variables. 
   The second component is applied to the replace map and the
   result conjoined with the defining formula 
   (used for field constraint analysis) *)
type extDecl = decl * (replaceMap -> form)

(** Scope of auxiliary quantified variables that are introduced during rewriting *)
type binderScope = 
  | Outermost (** bind auxiliary variable in the outermost scope wrt. to its defining formula *)
  | Innermost (** bind auxiliary variable innermost in the scope where the rewrite rule is applied *)

(** Auxiliary quantified variables introduced during rewriting *)
type auxDecl = form * bool * binderKind * binderScope * extDecl

(** Rewrite functions *)
type rewriteFun = 
    (bool -> typeEnv -> form -> form * auxDecl list) ->
    replaceMap -> bool -> typeEnv -> typeEnv -> form -> form * auxDecl list

(** Kinds of rewrite rules *)
type rewriteKind =
  | RewriteTerms (** rewrite terms within atomic formulas *)
  | RewriteAtoms (** rewrite atomic formulas *) 

(** Rewrite rules *)
type rewriteRule = rewriteFun * rewriteKind

let some_error f = "failure in rewriting of formula:\n" ^ string_of_form f
let msome_error msg f = "TermRewrite." ^ msg ^ ": failure in rewriting of formula:\n" ^ string_of_form f
let merror proc msg f = "TermRewrite." ^ proc ^ ": " ^ msg ^ ":\n" ^ string_of_form f

let get_type x env =
  try Util.find_map (fun (x', ty) -> if x = x' then Some ty else None) env
  with Not_found -> TypeUniverse


let type_of_term env t = 
  let ty = match t with
  | TypedForm(_, ty) -> ty
  | Var v -> get_type v env
  | _ -> TypeReconstruct.get_type env t
  in normalize_type ty

(** Constructs an extended variable declaration with a defining formula 
   that does not depend on the state of the replace map *)
let mk_const_decl (v : typedIdent) (decl_opt : form option) : extDecl =
  ((v, decl_opt), fun _ -> mk_true)

(** Constructors for auxiliary variables *)

let mk_inner_exists pol t edecl = 
  (t, pol, Exists, Innermost, edecl)
let mk_inner_forall pol t edecl = 
  (t, pol, Forall, Innermost, edecl)
let mk_outer_exists pol t edecl = 
  (t, pol, (if pol then Exists else Forall), Outermost, edecl)
let mk_outer_forall pol t edecl = 
  (t, pol, (if pol then Forall else Exists), Outermost, edecl)

let is_bound (v : ident) (env : typeEnv) = 
  List.exists (fun (v', _) -> v = v') env

let mk_unique_names (vs : typedIdent list) (env : typeEnv) (f : form) : (typedIdent list) * form =
  let vs', sigma = List.fold_right (fun (v, ty) (vs', sigma) ->
    if is_bound v env then
      let v' = Util.fresh_name "v" in
	((v', ty)::vs', (v, mk_var v')::sigma)
    else ((v, ty)::vs', sigma)) vs ([], [])
  in
  let f' = match sigma with [] -> f | _ -> subst sigma f in
    (vs', f')

let bind replace_map pol (aux_vars : auxDecl list) f env =
  let f' =
    List.fold_left (fun f' (t, pol', b, bs, ((vt, decl_opt), decl_constr)) ->
      let mk_binder, mk_decl = match b, pol, pol'  with
	| Exists, true, true | Exists, false, false | Forall, true, false | Forall, false, true ->
	    smk_exists, fun (f1, f2) -> 
	      (match f1 with 
		 | App (Const Or, f1s) -> 
		     smk_or (List.rev_map (fun f -> smk_and [f2; f]) f1s)
		 | _ -> smk_and [f1; f2])
	| Forall, true, true | Forall, false, false | Exists, true, false | Exists, false, true  ->
	    smk_foralls, smk_impl
	| Lambda, _, _ -> (fun (vs, f) ->
	    match f with
	      | Binder (Lambda, vs', f') -> Binder (Lambda, vs @ vs', f')
	      | _ -> Binder (Lambda, vs, f)), 
	    (fun (f1, f2) -> smk_and [f1; f2])
	| b, _, _ -> 
	    let mk_binder (vs, f) =
	      match f with
	      |	Binder (b', vs', f') when b = b' ->
		  Binder (b, vs' @ vs, f')
	      |	_ -> Binder (b, vs, f)
	    in
	    mk_binder, (fun (f1, f2) -> smk_and [f1; f2])
      in
      let _ = 
	try if FormHashtbl.find replace_map t = vt then 
	  FormHashtbl.remove replace_map t 
	with Not_found -> ()
      in
	mk_binder ([vt], mk_decl (smk_and ([safe_unsome mk_true decl_opt;decl_constr replace_map]), f'))) f aux_vars
      in
  let env' = List.filter (fun tv -> not (List.exists (fun (_, _, _, _, ((tv',_), _)) -> tv = tv') aux_vars)) env in
    (f', env')

let bind_outer replace_map genv pol b bvs (aux_vars : auxDecl list) f env =
  let contains t vs = List.exists (fun (x, _) -> 
    List.mem x (fv t) && not (is_bound x genv)) vs
  in
  let _, new_bound, aux_vars' = 
    List.fold_right (fun ((t, _, _, _, ((v, decl_opt), _)) as auxv) (vs, new_bound, aux_vars') ->
      if contains (mk_list [t; safe_unsome mk_true decl_opt]) (vs @ bvs) then
	(v::vs, auxv::new_bound, aux_vars')
      else
	(vs, new_bound, auxv::aux_vars')) aux_vars ([], [], [])
  in
  let bvs' = List.map (fun vt -> (mk_true, pol, b, Innermost, (mk_const_decl vt None))) bvs in
  let f', _ = bind replace_map pol (new_bound @ bvs') f env in
    (f', aux_vars')

(** [rewrite pol rewrite_rules genv f] successively applies a list of rewrite rules to formula [f]. 

   Parameters:
   [pol] polarity of the formula. The polarity determines the quantification of auxiliary variables.
   [rewrite_rules] the list of applied rewrite rules.
   [genv] the global environment which must contain  all free variables occuring in [f].
   [f] the formula to be rewritten

   Return value:
   The return value is the rewrittin formula and its new global environment. The new global environment is the 
   original environment extended with outermost bound auxiliary variables. 
   If [pol] is true these auxiliary variables are implicitly universally quantified, otherwise existentially.
 *)
let rewrite (pol : bool) (rewrite_rules : rewriteRule list) (genv : typeEnv) (f0 : form) :
    form * typeEnv =
  let replace_map = FormHashtbl.create 0 in
  let bind = bind replace_map in
  let extend_genv (aux_vars : auxDecl list) =
    let genv', defs, aux_vars' = List.fold_left 
	(fun (genv', defs, aux_vars') 
	    ((t, pol', b, k, ((vt, decl_opt), decl_constr)) as aux_var)  ->
	      match (b, pol, pol') with
	      | (Exists, false, false) | (Forall, true, true) 
	      |	(Forall, false, true) | (Exists, true, false) -> 
   		  FormHashtbl.remove replace_map t;
		  let def = smk_and [safe_unsome mk_true decl_opt; decl_constr replace_map] in
		  (vt::genv', def::defs, aux_vars')
	      | _ -> (genv', defs, aux_var::aux_vars')) 
	([], [], []) aux_vars
    in (List.rev_append genv' genv, defs, aux_vars')
  in
  let rec rewrite rewrite_rules pol env f =
  match rewrite_rules with
  | [] -> (f, [])
  | (r_cb, k)::rewrite_rules' ->
      let apply_to_terms = match k with RewriteTerms -> true | _ -> false in
      let r = r_cb (rewrite rewrite_rules) replace_map in
      let rewrite' = rewrite rewrite_rules' in 
      let bind_inner pol (aux_vars : auxDecl list list) f env =
	let outer_aux, inner_aux = 
	  List.partition (function (_, _, _, Outermost, _) -> true | _ -> false)
	    (List.concat aux_vars) 
	in
	let f', env' = bind pol inner_aux f env in
	let f'', aux_vars = rewrite' pol env' f' in
	(f'', aux_vars @ outer_aux)
      in
      let bind_outer = bind_outer replace_map genv in
      let extend_env env acc =
	List.rev_map (fun (_, _, _, _, ((vt, _), _)) -> vt) acc @ env 
      in
      let rec rewrite_atom pol env a =
	match a with
	(* Composed atoms *)
	| App (Const c, [t1; t2]) ->
	    (match c with
	    | Eq | Seteq | Subseteq | Subset | Elem
	    | Lt | Gt | LtEq | GtEq | Disjoint ->
 		let t1', acc1 = r pol genv env t1 in
		let env' = extend_env env acc1 in
		let t2', acc2 = r pol genv env' t2 in
		bind_inner pol [acc1; acc2] (App (Const c, [t1'; t2'])) (extend_env env' acc2)
	    | _ -> fail (msome_error "rewrite_atom" f))
	| _ -> let a', acc = r pol genv env a in
	  bind_inner pol [acc] a' (extend_env env acc)
      in
      let rec rewrite_form pol env f =
	match f with 
	(* Comments *)
	| App (Const Comment as c, [str; f]) ->
	    let f', aux_vars = rewrite_form pol env f in
	    (App (c, [str; f']), aux_vars)
        (* Boolean connectives *)
	| App (Const c, fs) ->
	    (match (c, fs) with 
	    | (Or, _) | (And, _) | (MetaAnd, _) -> 
		let fs', aux_vars = List.fold_right (fun f (fs', aux_vars) -> 
		  let f', aux_vars' = rewrite_form pol env f in (f'::fs', aux_vars' @ aux_vars)) fs ([], [])
		in (App (Const c, fs'), aux_vars)
	    | (Not, [f]) ->
		 let f', aux_vars = rewrite_form (not pol) env f in
		 (App (Const c, [f']), aux_vars)
	    | (Impl, [f1; f2]) | (MetaImpl, [f1; f2]) ->
		let f1', aux_vars1 = rewrite_form (not pol) env f1 in
		let f2', aux_vars2 = rewrite_form pol env f2 in
		(App (Const c, [f1'; f2']), aux_vars2 @ aux_vars1)
	    | (Iff, [f1; f2]) 
	    | (Eq, [TypedForm (_, TypeApp (TypeBool, [])) as f1; f2]) ->
		let f11, aux_vars11 = rewrite_form (not pol) env f1 in
		let f21, aux_vars21 = rewrite_form (not pol) env f2 in
		let f12, aux_vars12 = rewrite_form pol env f1 in
		let f22, aux_vars22 = rewrite_form pol env f2 in 
		if equal f11 f12 && equal f21 f22 then
		  (App (Const c, [f11; f21]), aux_vars21 @ aux_vars11)
                else
		  (smk_and [smk_impl (f11, f22);
			    smk_impl (f21, f12)], aux_vars12 @ aux_vars21) 
	    | _ when not (apply_to_terms) ->
		let f', acc = r pol genv env f in
		bind_inner pol [acc] f' env
	    | _ -> rewrite_atom pol env f)
	(* Binders *)
	| Binder (Exists as b, vs, f)
	| Binder (Forall as b, vs, f) ->
	    (* make names of bound variables unique *)
	    let vs', f' = mk_unique_names vs (env @ genv) f in
	    let env' = vs' @ env in
	    let f', aux_vars = rewrite_form pol env' f' in
	    let f', aux_vars' = bind_outer pol b vs' aux_vars f' env' in
	    (f', aux_vars')
	(* Predicates *) 
	| App (Var v as pred, es) 
	| App (TypedForm (Var v, _) as pred, es) when apply_to_terms ->
	    let arg_tys = match normalize_type (get_type v (env @ genv)) with
	    | TypeFun (arg_tys, _) -> arg_tys
	    | TypeApp (TypeArray, [arg_ty; _]) -> [arg_ty]
	    | TypeUniverse -> List.map (fun _ -> TypeUniverse) es
	    | _ -> fail (merror "rewrite" "type error (1)" f)
	    in
	    let es', accs, env', _ = List.fold_right (fun e (es', accs, env', tys) -> 
	      match tys with
	      |	ty::tys' ->
		  (match (normalize_type ty, e) with 
		  | (TypeApp (TypeBool, []), _) -> 
		      let e', acc = rewrite_form pol env' e in
		      (e'::es', acc::accs, extend_env env' acc, tys')
		  | (TypeFun (_, TypeApp (TypeBool, [])), Binder (Lambda, vs, f)) ->
		      let env'' = vs @ env' in
		      let f', acc = rewrite_form pol env'' f in
		      let e', acc = bind_outer pol Lambda (List.rev vs) acc f' env'' in
		      (e'::es', acc::accs, extend_env env' acc, tys')
		  | _ ->
		      let e', acc = r pol genv env' e in 
		      (e'::es', acc::accs, extend_env env' acc, tys'))
	      | _ -> fail (merror "rewrite" "type error (2)" e)) 
		es ([], [], env, List.rev arg_tys)
	    in bind_inner pol accs (App (pred, es')) env'
	| TypedForm (f, ty) -> 
	    let f', aux_vars = rewrite_form pol env f in
	    (TypedForm (f', ty), aux_vars)
	| _ when not apply_to_terms -> 
	    let f', acc = r pol genv env f in
	    bind_inner pol [acc] f' env
	| _ -> rewrite_atom pol env f
      in rewrite_form pol env f
  in 
  let f, aux_vars = rewrite rewrite_rules pol [] f0 in
  let genv', defs, aux_vars1 = extend_genv aux_vars in
  let f1, _ = bind pol aux_vars1 f [] in
  let f' = if pol then smk_impl (smk_and defs, f1) else smk_and (f1::defs) in
  (f', genv')

(** A rewrite rule is a tuple [(r,k)] where [r] is the actual rewrite
   function and [k] determines wether [r] is applied to atomic
   formulae or to non-boolean subterms of atomic formulae.

   Rewrite functions:
   A rewrite [r call_back replace_map pol genv env f] is as follows:
   [call_back] allows [r] to recursively call back [TermRewrite.rewrite] 
   [replace_map] a mapping from terms to typed identifiers which is used 
     for common subexpression elimination.
   [pol] the polarity of the context in which [f] occurs.
   [genv] the global environment of the context of [f]
   [env] the local environment of variables bound in the context of [f]
   [f] the formula to be rewritten

   Return value of rewrite functions: 
   The return value of a rewrite function is a pair [(f', aux_decls)]
   where [f'] is the rewritten formula and [aux_decls] is a list of
   declarations for auxilliary variables that are introduced during
   rewriting.  Rewrite rules can choose whether auxiliary variables
   are bound immediately in the calling context of the rewrite rule or
   whether they are bound in the outermost possible scope wrt. bound
   variables in defining formulas of aux. variables. Defining formulas
   of auxiliary variables are not further rewritten in
   [!Termrewrite.rewrite]. This can be accomplished by applying function
   [call_back] on defining formulae.

*)

(** Term rewrite rule for elimination of set comprehensions *)
(*
let rewrite_comprehensions : rewriteRule =
  let r = fun call_back replace_map pol genv env t ->
    let mk_quant = if pol then mk_inner_exists else mk_inner_exists in
    let rec rewrite t =
      match t with
      | Var v -> (t, [])
      | Const _ -> (t, [])
      | App (Const Comment as c, [str; t]) -> 
	let t', new_vars = rewrite t in
	(App (c, [str; t']), new_vars)
      | App (fun_t, ts) ->
	  let ts', new_vars = List.fold_right 
	      (fun t (ts', new_vars) ->
		let t', new_vars' = rewrite t in
		(t'::ts', new_vars' @ new_vars))
	      ts ([], [])
	  in
	  let fun_t', new_vars' = rewrite fun_t in 
	  (App (fun_t', ts'), new_vars' @ new_vars)	
      | Binder (Comprehension, vs, f) ->
	  let f', new_vars = call_back pol (vs @ env) f in
	  let t' =  Binder (Comprehension, vs, f') in
      	  let elem, elem_ty = match vs with
	  | [(v, ty)] -> (mk_var v, ty)
	  | _ -> let vars, tys = List.split vs in
	    (mk_tuple (List.map mk_var vars), mk_product_type tys)
	  in
	  (try (mk_var (fst (FormHashtbl.find replace_map t')), new_vars)
	  with Not_found ->
	    let set_var = Util.fresh_name "S" in
	    let t_rep = mk_var set_var in
	    let set_ty = mk_set_type elem_ty in
	    let decl = 
	      Some (smk_foralls (vs, mk_iff (mk_elem (elem, t_rep), f')))
	    in
	    let _ = FormHashtbl.add replace_map t' (set_var, set_ty) in
	    (t_rep, mk_quant pol t' (mk_const_decl (set_var, set_ty) decl) :: new_vars))
      | Binder (Lambda, vs, f) -> 
	  let f', new_vars = rewrite f in
	  let t' =  Binder (Lambda, vs, f') in
      	  (t', new_vars)
      | TypedForm (t, ty) -> 
	  let t', new_vars = rewrite t in
	  (TypedForm (t', ty), new_vars)
      | _ -> (t, [])
    in 
    match t with
    | Var _ | TypedForm (Var _, _) -> (t, [])
    | _ -> rewrite t
  in (r, RewriteTerms)
*)

(** Rewrite rule for eliminating non-atomic set expressions, set comprehensions and set equality *)
let rewrite_sets : rewriteRule = 
  let r call_back _ pol genv env f =
    let generate_elem 
	(ty : typeForm) 
	(elem_opt : form option) : form * typedIdent list = 
      match normalize_type ty with
      | TypeApp (TypeSet, [TypeVar _ as elemty])
      | TypeApp (TypeSet, [TypeApp (_, []) as elemty]) ->
	  let v = Util.fresh_name "v" in
	  (safe_unsome (mk_var v) elem_opt, [(v, elemty)])
      | TypeApp (TypeSet, [(TypeProd tys)]) -> (* Set of tuples *)
	  let vts = List.map (fun ty -> (Util.fresh_name "v", ty)) tys in
	  (safe_unsome (mk_tuple (List.map (fun (v, _) -> mk_var v) vts)) elem_opt, vts)
      | _ -> failwith ("\nrewrite_sets encountered unexpected type: " ^ (string_of_type ty) ^ "\n")
    in
    let transform_bound_tuples 
	(til : typedIdent list) : typedIdent list * substMap =
      List.fold_left
	(fun (acc, sm) (id, ty) ->
	   match ty with
	     | TypeProd tys ->
		 let ids = List.map (fun _ -> Util.fresh_name id) tys in
		 let tup = mk_tuple (List.map (fun v -> mk_var v) ids) in
		 let til = List.combine ids tys in
		   (acc @ til, sm @ [(id, tup)])
	     | _ -> (acc @ [(id, ty)], sm))
	([], []) til in
    let mk_compr vts ts' f0 =
      let vts, sm = transform_bound_tuples vts in
      let f = subst sm f0 in
      let m = match vts, ts' with
      |	[(v,_)], _ :: _ :: _ :: _ ->
	  (* v must have a product type *)
	  [(v, mk_tuple ts')]
      |	_ ->  
	  List.fold_right2 (fun (v1, _) t acc ->
	    (v1, t)::acc) vts ts' [] 
      in subst m f
    in
    let rewrite_setexp (elem : form) (tts : form list) (t : form) =
      let rec rewrite t =
	match normalize 1 t with
	| Const EmptysetConst -> (mk_false, [])
	| Const UniversalSetConst -> (mk_true, [])
	| App (Const FiniteSetConst, ts) ->
	    (smk_or (List.map (fun t -> mk_eq (t, elem)) ts), [])
	| App (Const Cap, ts) ->
	    let ts', aux = List.fold_right (fun t (ts', aux) ->
	      let t', aux' = rewrite t in (t'::ts', aux' @ aux)) ts ([], [])
	    in
	    (smk_and ts', aux) 
	| App (Const Cup, ts) -> 
	    let ts', aux = List.fold_right (fun t (ts', aux) ->
	      let t', aux' = rewrite t in (t'::ts', aux' @ aux)) ts ([], [])
	    in
	    (smk_or ts', aux)
	| App (Const Diff, [t1; t2]) -> 
	    let t1', aux1 = rewrite t1 in
	    let t2', aux2 = rewrite t2 in
	    (smk_and [t1'; smk_not t2'], aux2 @ aux1)
	| Binder (Comprehension, vts', f) ->
	    let f', aux = 
	      call_back pol (vts' @ env) f 
	    in (mk_compr vts' tts f', aux)
	| f -> (mk_elem (elem, t), [])
	     (* failwith ("unsupported set expression" ^ PrintForm.string_of_form f) *)
      in rewrite t
    in 
    let rec is_set_expr (f : form) : bool =
      match f with
	| Const EmptysetConst
	| App(Const FiniteSetConst, _)
	| App(Const Cap, _)
	| App(Const Cup, _)
	| App(Const Diff, _)
	| TypedForm(_, TypeApp (TypeSet, _))
	| Binder(Comprehension, _, _) -> true
	| App(Const Comment, [_; f']) ->
	    is_set_expr f'
	| _ -> false
    in
    let rewrite_subseteq_and_seteq
	(c : constValue)
	(t1 : form)
	(t2 : form)
	(ty : typeForm)
	(f : form) =
      let elem, vts = generate_elem ty None in
      let t1', aux1 = rewrite_setexp elem (List.map (fun (v, _) -> mk_var v) vts) t1 in
      let t2', aux2 = rewrite_setexp elem (List.map (fun (v, _) -> mk_var v) vts) t2 in
      let mk_form = match c with
	| Subseteq -> smk_impl
	| Seteq -> mk_iff
	| _ -> failwith ("Unexpected operator in : " ^ (PrintForm.string_of_form f) ^ "\n")
      in
      let f' = mk_foralls (vts, mk_form (t1', t2')) in
	(f', aux2 @ aux1) in
    let rewrite_subset (t1 : form) (t2 : form) (ty : typeForm) =
      let elem, vts = generate_elem ty None in
      let t1', aux1 = rewrite_setexp elem (List.map (fun (v, _) -> mk_var v) vts) t1 in
      let t2', aux2 = rewrite_setexp elem (List.map (fun (v, _) -> mk_var v) vts) t2 in
      let f' = mk_and [smk_foralls (vts, smk_impl (t1', t2')); 
		       smk_exists (vts, smk_and [t2'; smk_not t1'])] 
      in
	(f', aux2 @ aux1) in
    match f with
    | App (Const (Seteq as c), [TypedForm (t1, ty); TypedForm (t2, _)])
    | App (Const (Subseteq as c), [TypedForm (t1, ty); TypedForm (t2, _)])  ->
	(rewrite_subseteq_and_seteq c t1 t2 ty f)
    | App (Const (Seteq as c), [t1; t2])
    | App (Const (Subseteq as c), [t1; t2]) ->
	let ty = TypeReconstruct.get_type (env @ genv) t1 in
	(rewrite_subseteq_and_seteq c t1 t2 ty f)
    | App (Const Eq, [t1; t2]) when ((is_set_expr t1) || (is_set_expr t2)) ->
	let ty = TypeReconstruct.get_type (env @ genv) t1 in
	(rewrite_subseteq_and_seteq Seteq t1 t2 ty f)
    | App (Const Subset, [TypedForm (t1, ty); TypedForm (t2, _)])  ->
	(rewrite_subset t1 t2 ty)
    | App (Const Subset, [t1; t2]) ->
	let ty = (TypeApp (TypeSet, [TypeUniverse])) in
	  (rewrite_subset t1 t2 ty)
    | App (Const Elem, [t; TypedForm (App (Const Ite, [t1; t2; t3]), _)])
    | App (Const Elem, [t; App (Const Ite, [t1; t2; t3])]) ->
	let t1', aux1 = call_back pol env t1 in
	let t2', aux2 = call_back pol env (App (Const Elem, [t; t2])) in
	let t3', aux3 = call_back pol env (App (Const Elem, [t; t3])) in
	  (App (Const Ite, [t1'; t2';  t3']), aux1 @ aux2 @ aux3)
    | App (Const Elem, [t; TypedForm (Binder (Comprehension, vts', bf), _)])
    | App (Const Elem, [t; Binder (Comprehension, vts', bf)]) ->
	let bf', aux = call_back pol (vts' @ env) bf in
	let ts, vts', bf' = match normalize 1 t with
	| App (Const Tuple, ts) -> 
	    let vts', sm = transform_bound_tuples vts' in
	    let bf' = subst sm bf' in
	      ts, vts', bf' 
	| t' -> [t'], vts', bf'
	in
	  (let sigma = List.fold_right2 
	      (fun (v, _) t acc -> (v, t)::acc)
	      vts' ts []
	   in (subst sigma bf', aux))
    | App (Const Elem, [elem; TypedForm (t, ty)]) ->
	let elem, vts = generate_elem ty (Some elem) in
	(match ([elem], vts) with
	| (_ as ts, [_]) 
	| ([App (Const Tuple, ts)], _) -> rewrite_setexp elem ts t
	| _ ->
	    let ts = List.map (fun (v, _) -> mk_var v) vts in
            let t', aux = rewrite_setexp elem ts t in
	    let fvs = fv t' in
	      if (List.exists (fun (v,_) -> List.mem v fvs) vts) then
		(smk_exists (vts, smk_and [mk_eq (elem, mk_tuple ts); t']), aux)
	      else (t', aux))
    | App (Const Elem, [elem; App(_, _) as t]) ->
	let ty = TypeReconstruct.get_type (env @ genv) t in
	  call_back pol env (App (Const Elem, [elem; TypedForm(t, ty)]))
    | _ -> (f, [])
  in (r, RewriteAtoms)

(** Term rewrite rule for elimination of FieldRead and FieldWrite *)
let rewrite_FieldRead_FieldWrite : rewriteRule =
  let r call_back replace_map pol genv env t0 =
    let rec remove t upd_args = 
      match t with
      (* Comments *)
      | App (Const Comment as c, [str; t]) ->
	  let t', acc_t = remove t upd_args in
	  App (c, [str; t']), acc_t
      (* FieldRead *)
      | App (Const FieldRead, t :: ts) 
	-> remove (App (t, ts)) upd_args
      (* field write followed by field read on the same index *)  
      | App (App (Const FieldWrite, [_; ind; upd]), [arg]) 
      | App (TypedForm (App (Const FieldWrite, [_; ind; upd]), _), [arg]) when equal ind arg ->
	  let upd', acc_upd = remove upd None in
	  upd', acc_upd
      (* start of FieldWrite sequence *)
      | App (App (Const FieldWrite, _) as fld, [arg]) 
      | App (TypedForm (App (Const FieldWrite, _), _) as fld, [arg])
      | App (TypedForm (TypedForm (App (Const FieldWrite, _), _) as fld, _), [arg]) ->
	  let arg', acc_arg = remove arg None in
	  let ty = match type_of_term (env @ genv) fld with
	  | TypeFun (_, res_ty)
	  | TypeApp (TypeArray, [_; res_ty]) -> res_ty
	  | _ -> TypeUniverse in
	  let rhs = Util.fresh_name "v" in
	  let fld', acc_fld = remove fld (Some (arg', rhs, [], [], mk_true, ty)) in
	  mk_var rhs, List.concat [acc_fld; acc_arg]
      (* FieldWrite *)
      | App (Const FieldWrite, [fd; ind; upd]) ->
	  (match upd_args with
	  | Some (arg, rhs, inds, updates, guard, ty) ->
	      let ind', acc_ind = remove ind None 
	      and upd', acc_upd = remove upd None in
	      let g = mk_neq (ind', arg) in
	      let guard' = smk_and [g;guard] in
	      let eq_fun = match ty with
		| TypeApp(TypeSet, _) -> mk_seteq
		| _ -> mk_eq in
	      let update = 
		if List.mem ind' inds then mk_false else
		  let typed_upd = TypedForm (upd', ty) in
		  let typed_rhs = TypedForm (mk_var rhs, ty) in
		    mk_and [guard; mk_eq (ind', arg); eq_fun (typed_upd, typed_rhs)]
	      in
	      let fd', acc_fd = remove fd (Some (arg, rhs, ind'::inds, update::updates, guard', ty)) in
	      fd', List.concat [acc_fd; acc_ind; acc_upd]
	  | _ -> fail (msome_error "rewrite_FieldRead_FieldWrite.remove.upd_args" t0))
      | App (fld, args) -> 
	  let args', acc_args = 
	    List.fold_right (fun arg (args', acc_args) ->
	      let arg', acc_arg = remove arg None in
	      (arg' :: args', acc_arg :: acc_args)) args ([], [])
	  and fld', acc_fld = remove fld None in
	  App (fld', args'), List.concat acc_args
      | TypedForm (t, ty) -> 
	  let t', acc_t = remove t upd_args in
	  TypedForm (t', ty), acc_t
      | Binder (Comprehension, vs, f) -> 
	  let f', acc_f = call_back pol (vs @ env) f in
	  Binder (Comprehension, vs, f'), acc_f
      |	_ -> 
	  (match upd_args with
	  (* end of FieldWrite sequence *)
	  | Some (arg, rhs, _, updates, guard, ty) -> 
	      let upd_form = 
		mk_or
		  (smk_and [guard; mk_eq (App (t, [arg]), mk_var rhs)]
		   :: updates)
	      in 
	      let decl = Some upd_form in
	      t, [mk_inner_exists pol t (mk_const_decl (rhs, ty) decl)]
	  | _ -> t, [])
    in
    remove t0 None 
  in r, RewriteTerms

(** Term rewrite rule for unnesting of field applications *)
let rewrite_unnest : rewriteRule = 
  let r call_back replace_map pol genv env t =
    let rec flatten_term t new_vs =
      match t with
      | Var _ | Const _ -> (t, new_vs)
      | App (Const Comment as c, [str; t]) ->
	  let t', new_vs' = flatten_term t new_vs in
	  (App (c, [str; t']), new_vs')
      | App (fun_t, ts) ->
	  let res_ty = match type_of_term (env @ genv) fun_t with
	  | TypeFun (_, res_ty)
	  | TypeApp (TypeArray, [_; res_ty]) -> res_ty
	  | _ -> TypeUniverse
	  in
	  let fresh_v = Util.fresh_name "v" in
	  let v = Var fresh_v in
	  let ts', new_vs' = 
	    List.fold_right
	      (fun t (ts, new_vs) ->
		let t', new_vs' = flatten_term t new_vs in
		(t'::ts, new_vs'))  ts ([], new_vs)
	  in
	  let fun_t', new_vs' = 
	    flatten_term fun_t new_vs' in
	  let t' = App (fun_t', ts') in
	  let decl = Some (mk_eq (t', v)) in
	  (v, mk_inner_exists pol t' (mk_const_decl (fresh_v, res_ty) decl)::new_vs')
      | TypedForm (t, ty) -> 
	  let t', new_vs' = flatten_term t new_vs in
	  (TypedForm (t', ty), new_vs')
      |	Binder (Comprehension, vs, f) ->
	  let f', new_vs' = call_back pol (vs @ env) f in
	  (Binder (Comprehension, vs, f'), new_vs' @ new_vs)
      | _ -> (t, [])	  
    in match t with
    | Var _ -> (t, [])
    | _ -> flatten_term t []
  in (r, RewriteTerms)

(** Term rewrite rule for field constraint analysis. 
    Preconditions:                                            
   - all fields are atomic, i.e. in particular no FieldRead/FieldWrite                                    
   - field constraints are of the form (ALL v1 v2. f v1 = v2 --> F(v1,v2)) *)
let rewrite_derived_fields derived : rewriteRule =
  let r _ replace_map pol genv env t =
    let mk_annot f =
      match f with
      | TypedForm _ -> f
      | _ -> TypedForm (f, mk_object_type)
    in
    let is_derived_field fld = List.mem fld derived in
    let mk_eq_constraint fld x c replace_map =
      let fs = FormHashtbl.fold (fun t (c', _) acc ->
	match t with 
	| App (fld', [x']) when equal fld fld' ->
	    mk_impl (mk_eq (mk_annot x, mk_annot x'), mk_eq (mk_annot c, mk_annot (mk_var c')))::acc
	| _ -> acc) replace_map []
      in mk_and fs
    in
    let rec rewrite_ground_derived_fields t =
      match t with
      | Var v -> (t, [])
      | Const _ -> (t, [])
      | App (Const Comment as c, [str; t]) ->
	  let t', new_vars = rewrite_ground_derived_fields t in
	  (App (c, [str; t']), new_vars)
      | App (fun_t, ts) ->
	  let ts', new_vars = List.fold_right 
	      (fun t (ts', new_vars) ->
		let t', new_vars' = rewrite_ground_derived_fields t in
		(t'::ts', new_vars' @ new_vars))  
	      ts ([], [])
	  in
	  let t' = App (fun_t, ts') in
	  (match (fun_t, ts') with 
	  | (TypedForm (Var fld, _), [arg])
	  | (Var fld, [arg]) when is_derived_field fld  ->
	      let ty1, ty2 = (mk_object_type, mk_object_type) in
	      let const, new_vars' =
		try (mk_var (fst (FormHashtbl.find replace_map t')), new_vars)
		with Not_found ->
		  let fresh_c = Util.fresh_name "c_" in
		  let c = mk_var fresh_c in
		  let fdecl = Some (mk_eq (mk_annot t', mk_annot c)) in
		  let decl = ((fresh_c, ty2), fdecl) in
		  let new_var = mk_outer_forall pol t' (decl, mk_eq_constraint fun_t arg c) in
		  let _ = FormHashtbl.add replace_map t' (fresh_c, ty2) in
		  (c, new_var::new_vars)
	      in
	      (const, new_vars')
	  | _ -> (t', new_vars))
      | TypedForm (t, ty) -> 
	  let t', new_vars = rewrite_ground_derived_fields t in
	  (TypedForm (t', ty), new_vars)
      | _ -> fail (msome_error "rewrite_derived_fields" t)
    in 
    match t with
    | Var _ -> (t, [])
    | _ -> rewrite_ground_derived_fields t
  in (r, RewriteTerms)

(** Rewrite rule for elimination of atoms which do not fall into a specific theory.
   Precondition: annotated types, all terms flattend *)
let rewrite_non_theory_atoms 
    (is_theory_type : typeForm -> bool) 
    (is_theory_const : constValue -> bool) : rewriteRule = 
  let r call_back replace_map pol genv env a =
    (* let's have some fun with CPS *)
    let replace backtrack continue f =
      debug_lmsg 4 (fun () -> "abstracting part of formula:\n" ^ string_of_form f ^ "\n");
      try continue (mk_var (fst (FormHashtbl.find replace_map f)), [])
      with Not_found ->
	let ty = TypeReconstruct.get_type (env @ genv) f in
	if is_theory_type ty then
	  let fresh_c = Util.fresh_name "b_" in
	  let c = mk_var fresh_c in
	  let _ = FormHashtbl.add replace_map f (fresh_c, ty) in
	  continue (c, [mk_outer_forall pol f (mk_const_decl (fresh_c, ty) None)])
	else
	  (debug_lmsg 4 (fun () -> "backtracking...\n" ); backtrack ())
    in
    let rec abstract_forms backtrack continue = function
      |	[] -> continue ([], [])
      |	f::fs -> abstract_forms backtrack 
	    (fun (fs', auxv) -> abstract_form f backtrack (fun (f',auxv') -> 
	      continue (f':: fs', auxv @ auxv'))) fs 
    and abstract_form f backtrack continue =
      let _ = debug_lmsg 4 (fun () -> "checking formula:\n" ^ string_of_form f ^ "\n") in
      match f with
      | Const c | App (Const c, []) ->
	  if is_theory_const c then continue (f, [])
	  else replace backtrack continue f
      | Var v -> 
	  let ty = get_type v (env @ genv) in
	  if is_theory_type ty then continue (f, []) 
	  else 
	    let _ = debug_lmsg 4 (fun () -> "type:\n" ^ string_of_type ty ^ "\n") in
	    replace backtrack continue f
      | App (Const Comment, [s; f]) -> 
	  abstract_form f backtrack (fun (f',auxv) -> continue ((App (Const Comment, [s; f'])), auxv))
      | App (fn, ts) -> 
	  let backtrack' () = 
	    let _ = debug_lmsg 4 (fun () -> "backtracked to formula:\n" ^ string_of_form f) in
	    replace backtrack continue f in
	  abstract_form fn backtrack' (fun (fn', auxv) ->
	    abstract_forms backtrack' (fun (ts', auxv') ->
	      (continue (App (fn', ts'), auxv @ auxv'))) ts)
      | TypedForm (f, ty) -> 
	  if is_theory_type ty then abstract_form f backtrack (fun (f', auxv) ->
	    continue (TypedForm (f', ty), auxv))
	  else backtrack ()
      | _ -> replace backtrack continue f
    in 
    abstract_form a (fun () -> a, []) (fun (f, auxv) -> f, auxv)
  in (r, RewriteAtoms)


(** Rewrite rule for elimination of predicate "tree" using "rtrancl_pt" *)
let rewrite_tree : rewriteRule =
  let xs, ys, zs = 
    (Util.fresh_name "v", 
     Util.fresh_name "v", 
     Util.fresh_name "v")
  in
  let x, y, z = 
    (FormUtil.mk_var xs, 
     FormUtil.mk_var ys, 
     FormUtil.mk_var zs)     
  in 
  let r _ _ pol genv env f =
    let mk_tree parent_opt fields =
      let r flds x y = 
	FormUtil.smk_or 
	  (List.rev_map (fun fld -> mk_eq (App (fld, [x]), y)) flds) 
      in
      let r_pred flds = Binder (Lambda, [(xs, mk_object_type); (ys, mk_object_type)], r flds x y) in 
      let rtrancl_r flds x y = App (mk_var str_rtrancl, [r_pred flds; x; y]) in
(*      let trancl_r x y = App (mk_var str_trancl, [r_pred_nonull; x; y]) in *)
      let acyclic =
	match (parent_opt, fields) with
	| (Some fld, _) 
	| (None, [fld]) ->
	 (* use a simpler way to express acyclicity if backbone is a list *)
	    FormUtil.mk_foralls ([(xs, mk_object_type)], rtrancl_r [fld] x mk_null)
	| _ ->
	    mk_foralls 
	      ([(xs, mk_object_type); (ys, mk_object_type)],
	       smk_impl (smk_and [r fields x y; rtrancl_r fields y x], mk_eq (x, mk_null)))
      in
      let no_sharing =
	mk_foralls
	  ([(xs, mk_object_type); (ys, mk_object_type); (zs, mk_object_type)],
           mk_impl (smk_and [r fields z x; r fields y x; mk_neq (mk_null, x)],
                    mk_eq (y, z)))
      in
      let parent = 
	match parent_opt with
	| Some p ->
	    let parent1 = 
	      mk_foralls ([(xs, mk_object_type)],
			  FormUtil.mk_and
			    (List.rev_map (fun fld -> 
			      mk_or [mk_eq (App(p, [App(fld, [x])]), x); mk_eq (App(fld, [x]), mk_null)]) fields))
	    in
	    let parent2 =
	      mk_foralls ([(xs, mk_object_type); (ys, mk_object_type)],
			  mk_or [r fields (App(p, [x])) x; mk_and [mk_eq (App(p, [x]), mk_null); 
								   mk_impl (r fields y x, mk_eq (x, mk_null))]])
	    in
	    mk_comment "parent" (mk_and [parent1; parent2])
	| None -> mk_true
      in
      FormUtil.smk_and [mk_comment "acyclicity" acyclic; 
			mk_comment "no sharing" no_sharing;
			parent]
    in
    let mk_res f = (f, []) in
    match f with
    | App (Var p, [App (Form.Const ListLiteral, fields)])
    | App (TypedForm (Var p, _), [App (Form.Const ListLiteral, fields)]) 
      when p = str_tree ->
	mk_res (mk_tree None fields)
    | App (Var p, [fld; App (Form.Const ListLiteral, fields)])
    | App (TypedForm (Var p, _), [fld; App (Form.Const ListLiteral, fields)]) 
      when p = str_ptree ->
	mk_res (mk_tree (Some fld) fields)
    | _ -> mk_res f
  in (r, RewriteAtoms)

(** Expand pointsto relations *)
let rewrite_pointsto : rewriteRule =
  let mk_res f = (f, []) in
  let r _ _ pol genv env f =
    match f with
    | App (Var pointsto, [s1; f; s2]) 
    | App (TypedForm (Var pointsto, _), [s1; f; s2])
      when pointsto = points_to_name ->
	mk_res (mk_points_to_expansion s1 f s2)
    | _ -> mk_res f
  in (r, RewriteAtoms)


(** Rewrite rule for elimination of equality on functions *)
let rewrite_function_eq : rewriteRule =
  let r call_back replace_map pol genv env f =
    match f with
    | App (Const Eq, [TypedForm (t1, TypeFun (arg_tys, res_ty)); TypedForm (t2, _)])
    | App (Const Eq, [TypedForm (t1, TypeFun (arg_tys, res_ty)); t2])
    | App (Const Eq, [t2; TypedForm (t1, TypeFun (arg_tys, res_ty))]) ->
	let xts = List.map (fun ty -> (Util.fresh_name "varg", ty)) arg_tys in
	let aux = List.map (fun (v, ty) -> mk_inner_forall pol (mk_var v) (mk_const_decl (v, ty) None)) xts in
	let xs = List.map (fun (x, _) -> mk_var x) xts in
	let t1' = unlambda (TypedForm (App (t1, xs), res_ty))
	and t2' = unlambda (TypedForm (App (t2, xs), res_ty)) in
	let f' = disambiguate (mk_eq (t1', t2')) in
	f', aux
    | App (Const Eq, [TypedForm (t1, TypeApp (TypeArray,[arg_ty; res_ty])); TypedForm (t2, _)])
    | App (Const Eq, [TypedForm (t1, TypeApp (TypeArray, [arg_ty; res_ty])); t2])
    | App (Const Eq, [t2; TypedForm (t1, TypeApp (TypeArray, [arg_ty; res_ty]))]) ->
	let arg_tys, res_ty0 =
	  match res_ty with
	    | TypeApp (TypeArray, [arg_ty0; res_ty1]) ->
		[arg_ty; arg_ty0], res_ty1
	    | _ -> [arg_ty], res_ty in
	let xts = List.map (fun ty -> (Util.fresh_name "varg", ty)) arg_tys in
	let aux = List.map (fun (v, ty) -> mk_inner_forall pol (mk_var v) (mk_const_decl (v, ty) None)) xts in
	let xs = List.map (fun (x, _) -> mk_var x) xts in
	let t1' = unlambda (TypedForm (App (t1, xs), res_ty0))
	and t2' = unlambda (TypedForm (App (t2, xs), res_ty0)) in
	let f' = disambiguate (mk_eq (t1', t2')) in
	f', aux 
    | _ -> f, []
  in (r, RewriteAtoms)

(* Rewrites sets into predicates by rewriting elem's into function
   application. *)
let rewrite_elems (f : form) (env : typeEnv) : form * typeEnv =
  let rec rewrite_set_type (ty : typeForm) : typeForm =
    match ty with
      | TypeApp(TypeSet, tys) ->
	  let tys0 = List.map rewrite_set_type tys in
	    TypeFun(tys0, TypeApp(TypeBool, []))
      | TypeApp(st, tys) ->
	  TypeApp(st, (List.map rewrite_set_type tys))
      | TypeFun(tys, ty0) ->
	  let tys0 = List.map rewrite_set_type tys in
	  let ty1 = rewrite_set_type ty0 in
	    TypeFun(tys0, ty1)
      | TypeProd(tys) ->
	  TypeProd(List.map rewrite_set_type tys)
      | _ -> ty in
  let rewrite_env (env : typeEnv) : typeEnv =
    List.map (fun (id, ty) -> (id, (rewrite_set_type ty))) env in
  let rec rewrite_elems_rec (f : form) : form =
    match f with
      | App(Const Elem, [_; (Const EmptysetConst)])
      | App(Const Elem, [_; TypedForm(Const EmptysetConst, _)]) ->
	  Const (BoolConst false)
      | App(Const Elem, [f0; f1]) ->
	  App(rewrite_elems_rec f1, [rewrite_elems_rec f0])
      | App(Const FiniteSetConst, _)
      | App(Const Cap, _)
      | App(Const Cup, _)
      | App(Const Diff, _)
      | App(Const Seteq, _)
      | App(Const Subseteq, _)
      | Binder(Comprehension, _, _) ->
	  failwith ("rewrite_elems did not expect: " ^ (MlPrintForm.string_of_form f) ^ "\n")
      | App(f0, fs) ->
	  App(rewrite_elems_rec f0, List.map rewrite_elems_rec fs)
      | Binder(b, til, f0) ->
	  let ids, tys = List.split til in
	  let tys0 = List.map rewrite_set_type tys in
	  let til0 = List.combine ids tys0 in
	    Binder(b, til0, (rewrite_elems_rec f0))
      | TypedForm(f0, ty) ->
	  TypedForm((rewrite_elems_rec f0), (rewrite_set_type ty))
      | _ -> f in
    ((rewrite_elems_rec f), (rewrite_env env))
      
type tupleMap = (ident, form list) Hashtbl.t

(* Rewrites tuples into individual elements. A named tuple T is
   rewritten as t0, t1, ... etc. In order for this pass to work
   properly, it's important that sets have already been translated
   into predicates. *)
let rewrite_tuples (m : tupleMap) (f : form) (env : typeEnv) : form * typeEnv =
  let make_elems (id : ident) lst : form list =
    try Hashtbl.find m id
    with Not_found ->
      let elms = 
	List.map (fun f -> Var (Util.fresh_name (id ^ "_tup_"))) lst in
	Hashtbl.add m id elms; elms in
  let extract_id (f : form) : ident =
    match f with 
      | Var id
      | TypedForm(Var id, _) -> id 
      | _ -> failwith ("unexpected form: "^ (string_of_form f) ^ "\n") in
  let rec rewrite_tuple_ty (ty : typeForm) : typeForm =
    match ty with
      | TypeApp(st, tys) ->
	  TypeApp(st, rewrite_tuple_tys tys)
      | TypeFun(tys, ty) ->
	  TypeFun((rewrite_tuple_tys tys), (rewrite_tuple_ty ty))
      | _ -> ty
  and rewrite_tuple_tys (tys : typeForm list) : typeForm list =
    match tys with
      | [] -> []
      | ty :: tys_rest ->
	  let ty' = rewrite_tuple_ty ty in
	  let tys_rest' = rewrite_tuple_tys tys_rest in
	    match ty' with
	      | TypeProd tys_tup ->
		  tys_tup @ tys_rest'
	      | _ -> ty' :: tys_rest' in
  let rec rewrite_env (env : typeEnv) : typeEnv =
    match env with
      | [] -> []
      | (id, ty) :: ti_rest ->
	  let ty' = rewrite_tuple_ty ty in
	  let ti_rest' = rewrite_env ti_rest in
	    match ty' with
	      | TypeProd tys ->
		  let fs = make_elems id tys in
		  let ids = List.map extract_id fs in
		    (List.combine ids tys) @ ti_rest'
	      | _ -> (id, ty') :: ti_rest' in
  let rec rewrite_tuples_rec (f : form) : form = 
    match f with
    | App(Const Eq, [App(Const Tuple, fs0); App(Const Tuple, fs1)])
    | App(Const Eq, [TypedForm(App(Const Tuple, fs0), _); App(Const Tuple, fs1)])
    | App(Const Eq, [App(Const Tuple, fs0); TypedForm(App(Const Tuple, fs1), _)])
    | App(Const Eq, [TypedForm(App(Const Tuple, fs0), _); TypedForm(App(Const Tuple, fs1), _)]) ->
	let fs0' = List.map rewrite_tuples_rec fs0 in
	let fs1' = List.map rewrite_tuples_rec fs1 in
	  smk_and (List.map2 smk_eq fs0' fs1')
    | App(Const Eq, [App(Const Tuple, fs0); Var v])
    | App(Const Eq, [TypedForm(App(Const Tuple, fs0), _); Var v])
    | App(Const Eq, [App(Const Tuple, fs0); TypedForm(Var v, _)])
    | App(Const Eq, [TypedForm(App(Const Tuple, fs0), _); TypedForm(Var v, _)])
    | App(Const Eq, [Var v; App(Const Tuple, fs0)])
    | App(Const Eq, [TypedForm(Var v, _); App(Const Tuple, fs0)])
    | App(Const Eq, [Var v; TypedForm(App(Const Tuple, fs0), _)])
    | App(Const Eq, [TypedForm(Var v, _); TypedForm(App(Const Tuple, fs0), _)]) ->
	let fs0' = List.map rewrite_tuples_rec fs0 in
	let fs1 = make_elems v fs0 in
	  smk_and (List.map2 smk_eq fs0' fs1)
    | App(Const Elem, _) ->
	failwith ("rewrite_tuples_rec did not expect: " ^ (string_of_form f) ^ "\n")
    | App(f0, fs) ->
	App(rewrite_tuples_rec f0, rewrite_tuple_args fs)
    | Binder(b, til, f0) ->
	  Binder(b, (rewrite_env til), (rewrite_tuples_rec f0))
    | TypedForm(f0, ty) ->
	TypedForm(rewrite_tuples_rec f0, rewrite_tuple_ty ty)
    | _ -> f
  and rewrite_tuple_args (fs : form list) : form list =
    match fs with
      | [] -> fs
      | f0 :: f_rest ->
	  let f0' = rewrite_tuples_rec f0 in
	  let f_rest' = rewrite_tuple_args f_rest in
	    match f0' with
	      | TypedForm(App(Const Tuple, fs0), TypeProd tys) ->
		  let fs0' = List.map2 (fun f ty -> TypedForm(f, ty)) fs0 tys in
		    fs0' @ f_rest'
	      | App(Const Tuple, fs0) 
	      | TypedForm(App(Const Tuple, fs0), _) ->
		  fs0 @ f_rest'
	      | _ -> f0' :: f_rest' in
    ((rewrite_tuples_rec f), (rewrite_env env))

(** Rewrite rule for removal of Ite *)
let rewrite_fo_ite : rewriteRule =
  let rewritable_op (op : constValue) : bool =
    match op with
      | Eq | Elem
      | Subseteq | Subset | Seteq -> true
      | _ -> false in
  let set_op (op : constValue) : bool =
    match op with
      | Cap | Cup | Diff -> true
      | _ -> false in
  let r call_back replace_map pol genv env t =
    let rec rewrite f  =
      match f with
      | App(Const op, [App(Const Ite, [f1; f2; f3]); f4]) when rewritable_op op ->
	  let ft = smk_impl (f1, App(Const op, [f2; f4])) in
	  let ff = smk_impl (smk_not f1, App(Const op, [f3; f4])) in
	  let f' = smk_and [ft; ff] in
	    rewrite f'
      | App(Const op, [f4; App(Const Ite, [f1; f2; f3])]) when rewritable_op op ->
	  let ft = smk_impl (f1, App(Const op, [f4; f2])) in
	  let ff = smk_impl (smk_not f1, App(Const op, [f4; f3])) in
	  let f' = smk_and [ft; ff] in
	    rewrite f'
      | App(Const op1, [App(Const op2, [App(Const Ite, [f1; f2; f3]); f4]); f5]) 
	  when rewritable_op op1 && set_op op2 ->
	  let ft = smk_impl (f1, App(Const op1, [App(Const op2, [f2; f4]); f5])) in
	  let ff = smk_impl (smk_not f1, App(Const op1, [App(Const op2, [f3; f4]); f5])) in
	  let f' = smk_and [ft; ff] in
	    rewrite f'
      | App(Const op1, [App(Const op2, [f4; App(Const Ite, [f1; f2; f3])]); f5]) 
	  when rewritable_op op1 && set_op op2 ->
	  let ft = smk_impl (f1, App(Const op1, [App(Const op2, [f4; f2]); f5])) in
	  let ff = smk_impl (smk_not f1, App(Const op1, [App(Const op2, [f4; f3]); f5])) in
	  let f' = smk_and [ft; ff] in
	    rewrite f'
      | App(Const op1, [f5; App(Const op2, [App(Const Ite, [f1; f2; f3]); f4])]) 
	  when rewritable_op op1 && set_op op2 ->
	  let ft = smk_impl (f1, App(Const op1, [f5; App(Const op2, [f2; f4])])) in
	  let ff = smk_impl (smk_not f1, App(Const op1, [f5; App(Const op2, [f3; f4])])) in
	  let f' = smk_and [ft; ff] in
	    rewrite f'
      | App(Const op1, [f5; App(Const op2, [f4; App(Const Ite, [f1; f2; f3])])]) 
	  when rewritable_op op1 && set_op op2 ->
	  let ft = smk_impl (f1, App(Const op1, [f5; App(Const op2, [f4; f2])])) in
	  let ff = smk_impl (smk_not f1, App(Const op1, [f5; App(Const op2, [f4; f3])])) in
	  let f' = smk_and [ft; ff] in
	    rewrite f'
      | App(Const Ite, [f0; f1; f2]) ->
	  (try (mk_var (fst (FormHashtbl.find replace_map f)), [])
	  with Not_found ->
	    let v = Util.fresh_name "v" in
	    let v0 = Var v in
	    let f0', na0 = rewrite f0 in
	    let f1', na1 = rewrite f1 in
	    let f2', na2 = rewrite f2 in
	    let fpos = FormUtil.smk_impl (f0', FormUtil.mk_eq(v0, f1')) in
	    let fneg = FormUtil.smk_impl (FormUtil.mk_not f0', FormUtil.mk_eq(v0, f2')) in
	    let vdef = smk_and [fpos; fneg] in	    
	    let new_var = mk_outer_forall pol f (mk_const_decl (v, TypeUniverse) (Some vdef)) in
	    let _ = FormHashtbl.add replace_map f (v, TypeUniverse) in
	    (v0, new_var :: na0 @ na1 @ na2))
      | App(f0, fl0) -> 
	  let f1, na0 = rewrite f0 in
	  let fl1, na1 = List.fold_right 
	      (fun f (fl1, new_vars) ->
		let f', new_vars' = rewrite f in
		(f'::fl1, new_vars' @ new_vars))  
	      fl0 ([], [])
	  in
	  (App(f1, fl1), na0 @ na1)
      | TypedForm (f', ty) -> 
	  let f'', na = rewrite f' in
	  (TypedForm (f'', ty), na)
      | Binder(Comprehension as b, vs, f0) ->
	  let vs', f0' = mk_unique_names vs (env @ genv) f0 in
	  let env' = vs' @ env in
	  let f1, aux_vars = call_back true env' f0' in
	  let f1', aux_vars' = bind_outer replace_map genv pol b vs' aux_vars f1 env' in
	    (f1', aux_vars')
      | _ -> (f, [])
    in rewrite t
  in (r, RewriteAtoms)

(** Rewrite rule for giving names to lambda's not eliminated by
    beta-reduction so they can be handled by eta-conversion. *)
let rewrite_lambdas : rewriteRule =
  let r call_back replace_map pol genv env t =
    let rec rewrite t =
      match t with
	| App (Const Comment as c, [str; t]) ->
	    let t', new_vs' = rewrite t in
	      App(c, [str; t']), new_vs'
	| TypedForm(Binder(Lambda as b, vs, f), ty) ->
	    let vs', f' = mk_unique_names vs (env @ genv) f in
	    let env' = vs' @ env in
	    let f', aux_vars = match f' with
	      | TypedForm(_, TypeApp(TypeBool, [])) -> call_back true env' f'
	      | _ -> (f', []) in
	    let f', aux_vars = bind_outer replace_map genv pol b vs' aux_vars f' env' in
	    let f' = TypedForm(f', ty) in
	    (try
	       let bindings = FormHashtbl.fold (fun t' (v, _) acc -> (t', v)::acc) replace_map [] in
	       let _, v = List.find (fun (t', _) -> equal f' t') bindings in
		 (TypedForm(Var v, ty), aux_vars)
	     with Not_found ->
	       let fresh_v = Util.fresh_name "v" in
	       let v = Var fresh_v in
	       let _ = FormHashtbl.add replace_map f' (fresh_v, ty) in
	       let decl = Some (mk_eq (v, f')) in
	       let aux_var = mk_outer_forall pol f' (mk_const_decl (fresh_v, ty) decl) in
		 (TypedForm(v, ty), aux_var::aux_vars))
	| TypedForm(t, ty) ->
	    let t', new_vs' = rewrite t in
	      TypedForm(t', ty), new_vs'
	| App(fun_t, ts) ->
	    let ts', new_vars = List.fold_right 
	      (fun t (ts', new_vars) ->
		 let t', new_vars' = rewrite t in
		   (t'::ts', new_vars' @ new_vars))
	      ts ([], [])
	    in
	    let fun_t', new_vars' = rewrite fun_t in 
	      (App (fun_t', ts'), new_vars' @ new_vars)	
	| _ -> t, []
    in
      rewrite t
  in r, RewriteTerms

(** Rewrite rule that replaces modulo operator with multiplication *)
let rewrite_mod : rewriteRule =
  let r call_back replace_map pol genv env t =
    let rec rewrite t =
      match t with
	| App (Const Comment as c, [str; t]) ->
	    let t', new_vs' = rewrite t in
	      App(c, [str; t']), new_vs'
	| App (Const Mod, [t0; t1]) ->
	    let t0', aux_vars0 = rewrite t0 in
	    let t1', aux_vars1 = rewrite t1 in
	    let t' = mk_mod (t0', t1') in
	    let fresh_r = Util.fresh_name "v" in
	    let r = Var fresh_r in
	    let _ = FormHashtbl.add replace_map t' (fresh_r, mk_int_type) in
	    let fresh_q = Util.fresh_name "v" in
	    let q = Var fresh_q in
	    let decl = (** ''EX q. t0' = t1' * q + r'' **)
	      Some (mk_exists(fresh_q, mk_int_type, 
			      mk_eq (t0', mk_plus (mk_mult (t1', q), r)))) in
	    let aux_var = mk_outer_forall pol t' (mk_const_decl (fresh_r, mk_int_type) decl) in
	      (r, aux_var::aux_vars0 @ aux_vars1)
	| TypedForm(t, ty) ->
	    let t', new_vs' = rewrite t in
	      TypedForm(t', ty), new_vs'
	| App(fun_t, ts) ->
	    let ts', new_vars = List.fold_right 
	      (fun t (ts', new_vars) ->
		 let t', new_vars' = rewrite t in
		   (t'::ts', new_vars' @ new_vars))
	      ts ([], [])
	    in
	    let fun_t', new_vars' = rewrite fun_t in 
	      (App (fun_t', ts'), new_vars' @ new_vars)	
	| _ -> t, []
    in
      rewrite t
  in r, RewriteTerms
	    

