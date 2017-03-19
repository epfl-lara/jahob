(** Convert a BAPA formula from {!Form.form} into {!Alpha.form}. *)

open Form
open FormUtil
  
let bool_to_form (b : bool) : Alpha.form =
  if b then Alpha.True else Alpha.False
let attempt (approx : bool) (f : unit -> Alpha.form) : Alpha.form =
  try (f ()) with (_ as exc) -> 
    (Util.msg (Printexc.to_string exc);
     bool_to_form approx)

(** Main translation function from HOL (Form.form) to BAPA (Alpha.form). *)
let rec tr (approx : bool) (env : typeEnv) (f : form) : Alpha.form = match f with
  | App(Const Impl, [f1;f2])
  | App(Const MetaImpl, [f1;f2]) -> Alpha.Impl(tr (not approx) env f1,
					       tr approx env f2)
  | App(Const Iff,[f1;f2]) ->
      tr approx env (App(Const And, [App(Const Impl, [f1; f2]);
				     App(Const Impl, [f2; f1])]))
  | App(Const MetaAnd, fs)
  | App(Const And, fs) -> Alpha.And (List.map (tr approx env) fs)
  | App(Const Or, fs) -> Alpha.Or (List.map (tr approx env) fs)
  | App(Const Not, [f1]) -> Alpha.Not (tr (not approx) env f1)
  | Binder(b,vts,f1) -> tr_binders approx env b vts (tr approx env f1)
  | App(Const Lt, [f1;f2]) -> 
      attempt approx (fun () -> Alpha.Less(tri env f1, tri env f2))
  | App(Const Gt, [f1;f2]) -> tr approx env (App(Const Lt, [f2;f1]))
  | App(Const LtEq, [f1;f2]) -> attempt approx (fun () -> 
						  Alpha.Leq(tri env f1, tri env f2))
  | App(Const GtEq, [f1;f2]) -> tr approx env (App(Const LtEq, [f2;f1]))
  | App(Const Elem, [f1;f2])  (* this should work, at least for f1 a variable *)
  | App(Const Subseteq, [f1;f2]) ->
      attempt approx (fun () -> Alpha.Subseteq(trs env f1, trs env f2))
  | App(Const Seteq, [f1;f2]) ->
      attempt approx (fun () -> Alpha.Seteq(trs env f1, trs env f2))
  | App(Const Eq, [f1;f2]) -> 
      (match TypeReconstruct.get_type env f1 with
	 | TypeApp(TypeInt,[]) -> 
	     attempt approx (fun () -> Alpha.Inteq(tri env f1, tri env f2))
	 | TypeApp(TypeSet, [TypeApp(TypeObject,[])]) ->
	     attempt approx (fun () -> Alpha.Seteq(trs env f1, trs env f2))
	 | TypeApp(TypeObject,[]) ->
	     (let f1s = mk_singleton f1 in
	      let f2s = mk_singleton f2 in
		attempt approx (fun () -> Alpha.Seteq(trs env f1s, trs env f2s)))
	 | _ -> bool_to_form approx
      )
  | Const (BoolConst b) -> if b then Alpha.True else Alpha.False
(* quantifiers should update the type environment *)
  | _ -> 
      (Util.msg("APPROXIMATED AWAY formula " ^ MlPrintForm.string_of_form f);
       bool_to_form approx)

and tr_binders (approx : bool) (env : typeEnv) (b : binderKind) 
    (vts : Form.typedIdent list) (f : Alpha.form) : Alpha.form =
  List.fold_right (tr_binder approx env b) vts f
and tr_binder 
    (approx : bool) 
    (env : typeEnv) 
    (b : binderKind) 
    ((v,t) : Form.typedIdent) 
    (f : Alpha.form) : Alpha.form =
  match t with
    | TypeApp(TypeInt,[]) -> 
	(match b with 
	  | Forall -> Alpha.Bind(Alpha.Forallint,v,f)
	  | Exists -> Alpha.Bind(Alpha.Existsint,v,f)
	  | _ -> bool_to_form approx)
    | TypeApp(TypeSet, [TypeApp(TypeObject,[])]) ->
	(match b with 
	  | Forall -> Alpha.Bind(Alpha.Forallset,v,f)
	  | Exists -> Alpha.Bind(Alpha.Existsset,v,f)
	  | _ -> bool_to_form approx)
    | TypeApp(TypeObject,[]) ->
(*	tr_binder approx env b (v,TypeApp(TypeSet, [t])) f *) (* AM: That's wrong!*)
      (match b with
	  Forall -> Alpha.Bind(Alpha.Forallset,v,(Alpha.Impl((Alpha.Inteq(Alpha.Card (Alpha.Setvar v), (Alpha.Const 1))),f)))
	| Exists -> Alpha.Bind(Alpha.Existsset,v,(Alpha.And [(Alpha.Inteq(Alpha.Card (Alpha.Setvar v), (Alpha.Const 1)));f]))
	| _ -> bool_to_form approx
      )
    | _ -> bool_to_form approx

and tri (env : typeEnv) (f : form) : Alpha.intTerm = match f with
  | Var v -> Alpha.Intvar v
  | Const (IntConst c) -> Alpha.Const c
  | App(Const Plus, fs) -> Alpha.Plus (List.map (tri env) fs)
  | App(Const Minus, [f1;f2]) -> Alpha.Minus(tri env f1, tri env f2)
  | App(Const Mult, [Const (IntConst k); f2]) -> Alpha.Times(k, tri env f2)
  | App(Const Div, [f1; Const (IntConst k)]) -> Alpha.Div(tri env f1, k)
  | App(Const Card, [f1]) -> Alpha.Card (trs env f1)
  | _ -> failwith ("Approximated away formula " ^ PrintForm.string_of_form f ^ 
		  " in tri.")

and trs (env : typeEnv) (f : form) : Alpha.setTerm = match f with
  | Var v -> Alpha.Setvar v
  | Const EmptysetConst -> Alpha.Emptyset
  | Const UniversalSetConst -> Alpha.Fullset
  | App(Const Cup, fs) -> Alpha.Union (List.map (trs env) fs)
  | App(Const Cap, fs) -> Alpha.Inter (List.map (trs env) fs)
  | App(Const Diff, [f1;f2]) -> 
      (let f1t = trs env f1 in
       let f2ct = Alpha.Complement (trs env f2) in
	 Alpha.Inter [f1t; f2ct])
  | App(Const FiniteSetConst, [Var v]) -> Alpha.Setvar v
  | _ -> failwith ("Approximated away formula " ^ PrintForm.string_of_form f ^ 
		  " in trs.")

let universal_closure (f : Alpha.form) : Alpha.form =
  let mk_closed (v : ident) (f : Alpha.form) = Alpha.Bind(Alpha.Forallset,v,f) in
    List.fold_right mk_closed (Alpha.set_vars_of f) f

let rec get_singletons (env : typedIdent list) : ident list =
  match env with
    | [] -> []
    | (v,t)::env1 ->
	if is_object_type t then v :: get_singletons env1
	else get_singletons env1

let axiomatize_singletons (singletons : ident list) (f : Alpha.form) : Alpha.form =
  let mk_ax (x : ident) : Alpha.form =
    Alpha.Inteq(Alpha.Card (Alpha.Setvar x), Alpha.Const 1)
  in
    Alpha.Impl(Alpha.And (List.map mk_ax singletons), f)

(** if approx=false, generate stronger formula *)
let form_to_bapa (approx : bool) (env : typeEnv) (f0 : form) : Alpha.form = 
  let _ = Util.msg ("\nBAPA form input:\n" ^ 
		       PrintForm.string_of_form f0 ^ "\n That is:\n\n" ^
		       MlPrintForm.string_of_form f0 ^ "\n" ^ 
		       "\nenv =" ^ PrintForm.string_of_env env) in
  let singletons = get_singletons env in
  let _ = Util.msg("singletons = " ^ String.concat ", " singletons ^ "\n") in
  let f1 = tr approx env f0 in
  let res = universal_closure (axiomatize_singletons singletons f1) in
  let _ = Util.msg("BAPA translation done.\n") in
(*  let _ = Util.msg(Alpha.string_of_form res) in  *)
    res
