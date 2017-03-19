(** Type reconstruction a la Hindley/Milner. *)

open PrintForm
open Form
open FormUtil
open TypeVars

let debug_msg = Debug.debug_lmsg (Debug.register_debug_module "typeReconstruct")

let raise_error p msg f = 
  Debug.msg ("typeReconstruct.raise_error form ast: "
             ^ MlPrintForm.string_of_form f ^ "\n");
  Util.fail ("TypeReconstruct." ^ p ^ ": " ^ msg ^ ":\n"
        ^ PrintForm.string_of_form f)


let fresh_type_var () = TypeVar (Util.fresh_name "type")

(** [fresh_type_vars false t0]
      replaces universal types by different fresh type variables.
    [fresh_type_vars true t0]
      replaces universal types by different fresh type variables and already present type variables by fresh type variables, where same old type variables are replaced by the same fresh one.
*)
let fresh_type_vars keep_tvars t0 =
  let (subst : (ident * ident) list ref) = ref [] in
  let process_tvar (tvar : ident) =
   if keep_tvars then tvar else  
   try List.assoc tvar !subst 
    with Not_found ->
      (let fresh = Util.fresh_name "type" in
	 subst := (tvar, fresh) :: !subst;
	 fresh)
  in
  let rec walk t = match t with
      | TypeUniverse -> TypeVar (process_tvar (Util.fresh_name "a"))
      | TypeVar tv -> TypeVar (process_tvar tv)
      | TypeApp (t1, ts) -> TypeApp(t1, List.map walk ts)
      | TypeFun (ts, t1) -> TypeFun(List.map walk ts, walk t1)
      | TypeProd ts -> TypeProd (List.map walk ts)
  in 
  walk t0

let type_of_const =
  (* TODO: add types of missing constants *)
  let alpha = TypeVar "a" in
  let beta = TypeVar "b" in
  let ht = Hashtbl.create 10 in
  let _ = List.iter (Util.uncurry (Hashtbl.add ht))
      [(MetaImpl, mk_fun_type [mk_bool_type; mk_bool_type] mk_bool_type);
       (Impl, mk_fun_type [mk_bool_type; mk_bool_type] mk_bool_type);
       (Iff, mk_fun_type [mk_bool_type; mk_bool_type] mk_bool_type);
       (Not, mk_fun_type [mk_bool_type] mk_bool_type);
       (MetaEq, mk_fun_type [alpha; alpha] mk_bool_type);
       (Eq, mk_fun_type [alpha; alpha] mk_bool_type);
       (Ite, mk_fun_type [mk_bool_type; alpha; alpha] alpha);
       (Minus, mk_fun_type [alpha; alpha] alpha);
       (LtEq, mk_fun_type [alpha; alpha] mk_bool_type);
       (* integers *)
       (Lt, mk_fun_type [mk_int_type; mk_int_type] mk_bool_type);
       (Gt, mk_fun_type [mk_int_type; mk_int_type] mk_bool_type);
       (GtEq, mk_fun_type [mk_int_type; mk_int_type] mk_bool_type);
       (Plus, mk_fun_type [mk_int_type; mk_int_type] mk_int_type);
       (UMinus, mk_fun_type [mk_int_type] mk_int_type);
       (Mult, mk_fun_type [mk_int_type; mk_int_type] mk_int_type);
       (Div, mk_fun_type [mk_int_type; mk_int_type] mk_int_type);
       (Mod, mk_fun_type [mk_int_type; mk_int_type] mk_int_type);
       (* arrays *)
       (ArrayRead, mk_fun_type 
	  [mk_state_array alpha; mk_object_type; mk_int_type] alpha);
       (ArrayWrite, mk_fun_type 
	  [mk_state_array alpha; mk_object_type; mk_int_type; alpha]
	  (mk_state_array alpha));
       (* fields, objects *)
       (NullConst, mk_object_type);
       (FieldRead, mk_fun_type [mk_field_type alpha; mk_object_type] alpha);
       (FieldWrite, mk_fun_type [mk_field_type alpha; mk_object_type; alpha]
  			         (mk_field_type alpha));
       (* sets *)
       (Card, mk_fun_type [mk_set_type alpha] mk_int_type);
       (Cardeq, mk_fun_type [mk_set_type alpha; mk_int_type] mk_bool_type);
       (Cardleq, mk_fun_type [mk_set_type alpha; mk_int_type] mk_bool_type);
       (Cardgeq, mk_fun_type [mk_set_type alpha; mk_int_type] mk_bool_type);
       (EmptysetConst, mk_set_type alpha);
       (UniversalSetConst, mk_set_type alpha);
       (Elem, mk_fun_type [alpha; mk_set_type alpha] mk_bool_type);
       (Subseteq, mk_fun_type [mk_set_type alpha; mk_set_type alpha] mk_bool_type);
       (Subset, mk_fun_type [mk_set_type alpha; mk_set_type alpha] mk_bool_type);
       (Seteq, mk_fun_type [mk_set_type alpha; mk_set_type alpha] mk_bool_type);
       (Diff, mk_fun_type [mk_set_type alpha; mk_set_type alpha] 
                       (mk_set_type alpha));
       (Rtrancl, mk_fun_type [mk_set_type (mk_product_type [alpha; alpha])] 
	  (mk_set_type (mk_product_type [alpha; alpha])));
       (Rimage, mk_fun_type [mk_set_type (mk_product_type [alpha; beta]); mk_set_type alpha] (mk_set_type beta));
       (* others *)
       (Unit, mk_unit_type);
       (Comment, mk_fun_type [mk_string_type; mk_bool_type] mk_bool_type);
       (Old, mk_fun_type [alpha] alpha)
     ]
  in fun c n -> 
    match c with
    | BoolConst _ -> mk_bool_type
    | IntConst _ -> mk_int_type
    | StringConst _ -> mk_string_type
    | MetaAnd | And | Or -> 
	mk_fun_type (Util.generate_list (fun _ -> mk_bool_type) n) mk_bool_type
    | Cup | Cap -> 
	let ty = mk_fun_type (Util.generate_list (fun _ -> mk_set_type alpha) n) (mk_set_type alpha) in
	fresh_type_vars false ty
    | FiniteSetConst ->
	let ty = mk_fun_type (Util.generate_list (fun _ -> alpha) n) (mk_set_type alpha) in
	fresh_type_vars false ty
    | Tuple ->
	let tys = Util.generate_list (fun _ -> fresh_type_var ()) n in
	mk_fun_type tys (mk_product_type tys)
    | ListLiteral ->
	let arg_tys = Util.generate_list (fun _ -> alpha) n in
	let ty = mk_fun_type arg_tys (mk_list_type alpha) in
	fresh_type_vars false ty
    | _ -> 
	try fresh_type_vars false (Hashtbl.find ht c) 
	with Not_found -> raise_error "get_type_of_const" "type of constant unknown" (Const c)

let type_of_var =
  (* let alpha = TypeVar "a" in *)
  let ht = Hashtbl.create 2 in
  let _ = List.iter (Util.uncurry (Hashtbl.add ht)) 
      [(str_rtrancl, fun _ -> FormUtil.typeOf_pseudoconst_rtrancl);
       (str_tree, fun _ -> FormUtil.typeOf_pseudoconst_tree);
       (str_ptree, fun _ -> FormUtil.typeOf_pseudoconst_ptree)]
  in fun local_env global_env v n ->
  let get_type v = 
    try List.assoc v local_env 
    with Not_found -> Hashtbl.find global_env v
  in 
  try 
    let ty = fresh_type_vars false (Hashtbl.find ht v n) 
    in Hashtbl.replace global_env v ty; ty
  with  Not_found ->
      (* let _ = print_endline v in *)
    try  get_type v
    with Not_found -> 
      let ty = fresh_type_var () in
      Hashtbl.replace global_env v ty; ty

(** [is_monomorphic t]
    determines whether a type term does not contain type universes or free type variables. *)
let rec is_monomorphic = function
  | TypeUniverse | TypeVar _ -> false
  | TypeFun (arg_tys, res_ty) ->
      List.for_all is_monomorphic (res_ty :: arg_tys)
  | TypeApp (_, tys) 
  | TypeProd tys ->
      List.for_all is_monomorphic tys

(** [subst_type subst_map ty]
    replaces free type variables in ty according to the substitution map subst_map once. *)
let subst_type subst_map ty =
  let rec st ty = match ty with
  | TypeUniverse -> ty
  | TypeFun (arg_tys, res_ty) -> 
      let arg_tys' = List.map st arg_tys in
      TypeFun (arg_tys', st res_ty)
  | TypeApp (sty, tys) ->
      let tys' = List.map st tys in
      TypeApp (sty, tys')
  | TypeProd tys ->
      let tys' = List.map st tys in
      TypeProd tys'
  | TypeVar v -> 
      try Hashtbl.find subst_map v
      with Not_found -> ty
  in st ty
     
let subst_types_in_form subst_map f =
  let rec st f = match f with
  | Var _ | Const _ -> f
  | App (fn, fs) -> App (st fn, List.map st fs)
  | Binder (b, vts, f') -> 
      let vts' = List.map (fun (v, ty) -> (v, subst_type subst_map ty)) vts in
      Binder (b, vts', st f')
  | TypedForm (TypedForm (f, _), ty)
  | TypedForm (f, ty) -> TypedForm (st f, subst_type subst_map ty)
  in st f

let print_subst subst_map = 
  Hashtbl.iter (fun v ty -> Printf.printf "%s -> %s\n" v (PrintForm.string_of_type ty)) subst_map
  
let print_constraint ((ty1, ty2), f) =
  Printf.printf "%s = %s in %s\n" 
    (PrintForm.string_of_type ty1) 
    (PrintForm.string_of_type ty2) 
    (PrintForm.string_of_form f)

let type_error (ty1, ty2) f mgu = 
  raise_error "solve_constraints" 
    (Printf.sprintf "type error\ntried to match type\n\t%s\nwith type\n\t%s\nin formula" 
       (PrintForm.string_of_type ty1) (PrintForm.string_of_type ty2)) (subst_types_in_form mgu f) 

let simplify_constraints cs mono_mgu =
  let rec simplify acc = function
    | [] -> List.rev acc
    | ((ty1, ty2), f) :: cs ->
	let ty1' = subst_type mono_mgu ty1 in
	let ty2' = subst_type mono_mgu ty2 in
	try
	  match ty1', ty2' with
	  | TypeFun (arg_tys1, res_ty1), TypeFun (arg_tys2, res_ty2) ->
	      let cs' = List.fold_left2 (fun cs' ty1 ty2 -> ((ty1, ty2), f) :: cs') cs (res_ty1 :: arg_tys1) (res_ty2 :: arg_tys2) in
	      simplify acc cs'
	  | TypeApp (sty1, arg_tys1), TypeApp (sty2, arg_tys2) when sty1 = sty2 ->
	      let cs' = List.fold_left2 (fun cs' ty1 ty2 -> ((ty1, ty2), f) :: cs') cs arg_tys1 arg_tys2 in
	      simplify acc cs'
	  | TypeVar v, ty' 
	  | ty', TypeVar v when is_monomorphic ty' ->
	      Hashtbl.add mono_mgu v ty'; 
	      simplify acc cs
	  | _ -> 
	      if equal_types ty1' ty2' then
		simplify acc cs
	      else 
		simplify (((ty1', ty2'), f) :: acc) cs
	with Invalid_argument _ -> simplify (((ty1', ty2'), f) :: acc) cs
  in simplify [] cs

let solve_constraints cs mono_mgu =
  (* let _ = List.iter print_constraint cs in
  let _ = print_newline () in *)
  let subst_type mgu ty =
    subst_type mgu (subst_type mono_mgu ty)
  in
  let mgu = Hashtbl.create (List.length cs / 2) in
  (* Printf.printf "%d %d\n" (List.length cs) (List.length remaining_cs); *)
  let occur_error f = raise_error "solve_constraints" "occurs check failed" (subst_types_in_form mgu f) in
  let add_subst v ty cs f =
    if List.mem v (ftv ty) then occur_error f 
    else begin
      Hashtbl.replace mgu v ty;
      Hashtbl.iter (fun v' ty' -> Hashtbl.replace mgu v' (subst_type mgu ty')) mgu; 
      cs
    end
  in
  (* let type_error tys f = print_subst mgu; type_error tys f in *)
  let rec solve cs =
    match cs with
    | (tys, f)::cs' -> 
	(match tys with
	| (TypeApp (TypeArray, [arg_ty1; res_ty1]),
	   TypeFun (arg_ty2::arg_tys2, res_ty2))
	| (TypeFun (arg_ty2::arg_tys2, res_ty2),
	   TypeApp (TypeArray, [arg_ty1; res_ty1])) ->
	     solve (((arg_ty1, arg_ty2), f) :: 
		    ((res_ty1, TypeFun (arg_tys2, res_ty2)), f) :: cs')
	| (TypeApp (st1, tys1), TypeApp (st2, tys2)) when st1 = st2 ->
	    let new_cs = try
	      List.fold_left2 (fun cs ty1 ty2 -> ((ty1, ty2), f)::cs) cs' tys1 tys2 
	    with Invalid_argument _ -> type_error tys f mgu
	    in solve new_cs
	| (TypeProd tys1, TypeProd tys2) ->
	    let new_cs = try
	      List.fold_left2 (fun cs ty1 ty2 -> ((ty1, ty2), f)::cs) cs' tys1 tys2 
	    with Invalid_argument _ -> type_error tys f mgu
	    in solve new_cs
	| (TypeFun ([], ty1), ty2)
	| (ty1, TypeFun ([], ty2)) -> solve (((ty1, ty2), f) :: cs')
	| (TypeFun (arg_ty1::arg_tys1, res_ty1), 
	   TypeFun (arg_ty2::arg_tys2, res_ty2)) ->
	  solve (((arg_ty1, arg_ty2), f) :: ((TypeFun (arg_tys1, res_ty1), TypeFun (arg_tys2, res_ty2)), f) :: cs')
	| ((TypeVar v as ty1), ty2)
	| (ty2, (TypeVar v as ty1)) ->
	    if not (ty1 = ty2) then 
	      let ty1' = subst_type mgu ty1 in
		 if ty1 = ty1' then
		   let ty2' = subst_type mgu ty2 in
		     if ty1' = ty2' then solve cs'
		     else solve (add_subst v ty2' cs' f)
		 else solve (((ty1', subst_type mgu ty2), f) :: cs')
	    else solve cs'
	| _ -> type_error tys f mgu
	)
    | [] -> Hashtbl.iter (fun v ty -> Hashtbl.replace mono_mgu v ty) mgu; mono_mgu
  in solve cs


let infer_types global_env f =
  let _ = debug_msg 2 (fun () -> PrintForm.string_of_form f) in 
  let env = Hashtbl.create 0 in
  let mgu = Hashtbl.create 0 in
  let add_var (v, ty) =
    let ty' = fresh_type_vars true ty in
    Hashtbl.replace env v ty'; (v, ty')
  in
  let annotate_type f ty = match f with
  | TypedForm (f0, _) -> TypedForm (f0, ty)
  | _ -> TypedForm (f, ty)
  in
  let _ = List.rev_map add_var global_env in
  let add_constraint cs ty1 ty2 f =
    if not (equal_types ty1 ty2) then 
      (* let _ = 
	Printf.printf "  %s = %s in %s\n" 
	  (PrintForm.string_of_type ty1) 
	  (PrintForm.string_of_type ty2) 
	  (string_of_form f)
      in *)
      ((ty1, ty2), f) :: cs
    else cs
  in
  let rec res_type cs fn_ty arg_tys f =
    let rec match_types cs arg_tys1 arg_tys2 res_ty =
      match (arg_tys1, arg_tys2) with
      | (ty1::arg_tys1, ty2::arg_tys2) -> 
	  match_types (add_constraint cs ty1 ty2 f) arg_tys1 arg_tys2 res_ty
      |	(ty1::_, []) -> cs, TypeFun (arg_tys1, res_ty)
      |	([], []) -> cs, res_ty
      |	([], _) -> res_type cs res_ty arg_tys2 f
    in match fn_ty with
    | TypeFun (arg_tys1, res_ty) -> 
	match_types cs arg_tys1 arg_tys res_ty
    | TypeApp (TypeArray, [arg_ty; res_ty]) -> 
	match_types cs [arg_ty] arg_tys res_ty 
    | _ -> let res_ty = fresh_type_var () in 
      add_constraint cs fn_ty (TypeFun (arg_tys, res_ty)) f, res_ty
  in
  let rec gen cs local_env f =
    match f with 
    | Var v -> f, type_of_var local_env env v 0, cs
    | Const c -> f, type_of_const c 0, cs
    | App (fn, args) ->
	let fn', fn_ty, cs0 = 
	  match fn with
	  | Const c -> fn, type_of_const c (List.length args), cs
	  | Var v -> fn, type_of_var local_env env v (List.length args), cs
	  | _ -> gen cs local_env fn 
	in
	let args', arg_tys, cs1 = 
	  List.fold_right 
	    (fun t (args', arg_tys, cs) ->
	      let t', ty, cs' = gen cs local_env t in
	      t' :: args', ty :: arg_tys, cs') 
	    args ([], [], cs0)
	in
	let cs2, res_ty = res_type [] fn_ty arg_tys f in
	let cs2' = simplify_constraints cs2 mgu in
	let cs' = List.rev_append cs2' cs1 in
	(* add type annotations to polymorphic operators *)
	let f' = match fn with 
	| Const Eq | Const Seteq | Const LtEq | Const Minus | Const Elem 
	| Const Subseteq | Const Subset -> 
	    let typed_args = List.map2 (fun f ty -> annotate_type f ty) args' arg_tys 
	    in App (fn', typed_args)
	| _ -> App (fn', args')
	in f', res_ty, cs'
    | TypedForm (f, ty) ->
	let f', ty', cs' = match f with
	| Var v when not (List.mem_assoc v local_env || Hashtbl.mem env v) ->
	    let v, ty' = add_var (v, ty) in
	    let cs' = 
	      if is_monomorphic ty' then cs else 
	      add_constraint cs ty ty' f
	    in
	    f, ty', cs'
	| Var v ->
	    let cs' =
	      if ty = TypeUniverse then cs else 
	      add_constraint cs ty (type_of_var local_env env v 0) f
	    in 
	    f, ty, cs'
	| _ ->	
	    let f', ty', cs0 = gen cs local_env f in
	    let cs' =
	      if ty = TypeUniverse then cs0
	      else add_constraint cs0 ty ty' f
	    in
	    f', ty, cs'
	in annotate_type f' ty', ty', cs'
    | Binder (b, vts, bf) ->
	let vts', tys' = List.fold_right (fun (v, ty) (vts', tys') -> 
	  let ty' = fresh_type_vars true ty in
	  ((v, ty') :: vts' , ty' :: tys')) vts ([], []) in
	let bf', ty_bf, cs0 = gen cs (vts' @ local_env) bf in
	let cs', binder_ty = match b with
	| Exists | Forall ->
	    add_constraint cs0 mk_bool_type ty_bf f,
	    mk_bool_type
	| Comprehension ->
	    add_constraint cs0 mk_bool_type ty_bf f,
	    (match tys' with
	    | [ty] -> mk_set_type ty 
	    | _ -> mk_set_type (mk_product_type tys'))
	| Lambda -> cs0, TypeFun (tys', ty_bf)
	in
	Binder (b, vts', bf'), binder_ty, cs'
        (*
        match b with
	    Exists | Forall -> Binder(b,vts',bf'), mk_bool_type, (add_constraint cs0 mk_bool_type ty_bf f)
	  | Comprehension ->
	    let f' = Binder(b,vts',bf') in
	    let binder_ty = (match tys' with
	      | [] -> mk_set_type (fresh_type_var ())
	      | [ty] -> mk_set_type ty 
	      | _ -> mk_set_type (mk_product_type tys')) in
	    ((annotate_type f' binder_ty), binder_ty, (add_constraint cs0 mk_bool_type ty_bf f))
	  | Lambda ->
	    Binder(b,vts',bf'), TypeFun (tys', ty_bf), cs0
	*)
  in
  let f', f_ty, type_constraints = gen [] [] f in
  let global_env' = Hashtbl.fold
      (fun v ty env' -> (v, ty)::env') env []
  in
  f', global_env', f_ty, type_constraints, mgu


(** [get_env f] compute the global environment for formula [f] *)
let get_env f =
   let _, env, _, type_constraints, mgu0 = infer_types [] f in
   let mgu = solve_constraints type_constraints mgu0 in
   List.map (fun (v, ty) -> (v, subst_type mgu ty)) env


(** [well_typed env f] check whether formula [f] is well-typed in environment [env] *)
let well_typed env f =
  try
    let f', _, _, type_constraints, mgu0 = infer_types env f in
    ignore (solve_constraints type_constraints mgu0); true
  with Failure msg -> Util.warn msg; false

(** [get_type env f] get the type of [f] for environment [env] *)
let get_type env f =
  let f', _, f_ty, type_constraints, mgu0 = infer_types env f in
  let mgu = solve_constraints type_constraints mgu0 in
  subst_type mgu f_ty

(** [reconstruct_types env f] reconstruct types in formula [f] and environment [env] *) 
let reconstruct_types env f =
  let _ = debug_msg 0 (fun () -> "Reconstructing types...\n") in
  let f', env', _, type_constraints, mgu0 = infer_types env f in
  let mgu = solve_constraints type_constraints mgu0 in
  (* let _ = print_subst mgu in *)
  let f'' = subst_types_in_form mgu f' in 
  let env'' = List.map (fun (v, ty) -> (v, subst_type mgu ty)) env' in 
  let _ = debug_msg 0 (fun () -> "\nType reconstruction done.\n") in
  (f'', env'')

(** [disambiguate f] resolve ad-hoc polymorphism in [f] as much as possible *)
let disambiguate f =
  let rec da f = match f with
  | Var _ 
  | Const _ -> f
  | App (Const c, [TypedForm (t1, t1_ty) as tt1; tt2]) ->
      let tt1' = da tt1
      and tt2' = da tt2 in
      let c' = match (c, t1_ty) with
      |	(MetaEq, TypeApp (TypeBool, []))
      |	(Eq, TypeApp (TypeBool, [])) -> Iff
      | (MetaEq, TypeApp (TypeSet, _))
      | (Eq, TypeApp (TypeSet, _)) -> Seteq
      |	(LtEq, TypeApp (TypeSet, _)) -> Subseteq
      |	(Minus, TypeApp (TypeSet, _)) -> Diff
      |	_ -> c
      in App (Const c', [tt1'; tt2']) 
  | App(Const Eq, ([Const EmptysetConst; _] as args))
  | App(Const Eq, ([_; Const EmptysetConst] as args)) ->
      App(Const Seteq, args)
  | TypedForm (f, ty) -> TypedForm (da f, ty)
  | App (fn, args) -> App (da fn, List.map da args)
  | Binder (b, vts, f) -> Binder (b, vts, da f)
  in da f


