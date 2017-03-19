open Common
open Form
open FormUtil
open TypeReconstruct
open TermRewrite

(** Convert a Presbuger arirthmetic formula (in BAPA syntax tree) back
    to {!Form.form} formula to enable the use of CVC Lite *)
let bapa_to_form (f : Alpha.form) : form =
  let natural v = mk_lteq(mk_int 0, mk_var v) in
  let rec tr (f : Alpha.form ) : form = match f with
    | Alpha.PropVar id -> mk_var id
    | Alpha.True -> mk_true
    | Alpha.False -> mk_false
    | Alpha.Not f1 -> smk_not (tr f1)
    | Alpha.And fs -> smk_and (List.map tr fs)
    | Alpha.Or fs -> smk_or (List.map tr fs)
    | Alpha.Impl(f1,f2) -> smk_impl(tr f1, tr f2)
    | Alpha.Bind(Alpha.Forallset,v,f1) -> smk_forall(v,mk_obj_set_type,tr f1)
    | Alpha.Bind(Alpha.Existsset,v,f1) -> smk_exist(v,mk_obj_set_type,tr f1)
    | Alpha.Bind(Alpha.Forallint,v,f1) -> smk_forall(v,mk_int_type,tr f1)
    | Alpha.Bind(Alpha.Existsint,v,f1) -> smk_exist(v,mk_int_type,tr f1)
    | Alpha.Bind(Alpha.Forallnat,v,f1) -> 
	mk_forall(v,mk_int_type,mk_impl(natural v, tr f1))
    | Alpha.Bind(Alpha.Existsnat,v,f1) -> 
	mk_exists(v,mk_int_type,mk_and[natural v;tr f1])
    | Alpha.Bind(Alpha.ForallProp,v,f1) -> smk_forall(v,mk_bool_type,tr f1)
    | Alpha.Bind(Alpha.ExistsProp,v,f1) -> smk_exist(v,mk_bool_type,tr f1)
    | Alpha.Less(i1,i2) -> mk_lt(tri i1, tri i2)
    | Alpha.Leq(i1,i2) -> mk_lteq(tri i1, tri i2)
    | Alpha.Inteq(i1,i2) -> mk_eq(tri i1, tri i2)
    | Alpha.Seteq(s1,s2) -> mk_seteq(trs s1, trs s2)
    | Alpha.Subseteq(s1,s2) -> mk_subseteq(trs s1, trs s2)
  and tri (i : Alpha.intTerm) : form = match i with
    | Alpha.Intvar v -> mk_var v
	(*
	if v="MAXC" then mk_card mk_univ else mk_var v
	*)
    | Alpha.Const c -> mk_int c
    | Alpha.Plus [] -> mk_int 0
    | Alpha.Plus is -> Util.fold_right1pair smk_plus (List.map tri is)
    | Alpha.Minus(i1,i2) -> mk_minus(tri i1, tri i2)
    | Alpha.Times(c, i1) -> mk_mult(mk_int c, tri i1)
    | Alpha.Div(i1, c) -> mk_div(tri i1, mk_int c)
    | Alpha.Card s -> mk_card (trs s)
    | Alpha.IfThenElse(f1,i1,i2) -> smk_ite(tr f1, tri i1, tri i2)
  and trs (s : Alpha.setTerm) : form = match s with
    | Alpha.Setvar v -> mk_var v
    | Alpha.Emptyset -> mk_obj_emptyset
    | Alpha.Fullset -> mk_obj_univ
    | Alpha.Complement s -> mk_setdiff(mk_obj_univ,trs s)
    | Alpha.Union [] -> mk_obj_emptyset
    | Alpha.Union ss -> Util.fold_right1pair mk_cup (List.map trs ss)
    | Alpha.Inter [] -> mk_obj_univ
    | Alpha.Inter ss -> Util.fold_right1pair mk_cap (List.map trs ss)
  in tr f

let show_bf (f : Alpha.form) : unit =
  Util.msg ("\n" ^ PrintForm.string_of_form (bapa_to_form f) ^ "\n")
