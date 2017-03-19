(**
   Conversion from BAPA (boolean algebras with Presburger arithmetic) sentences
   into PA (pure Presburger arithmetic) sentences.  
   Shows that BAPA is decidable and elementary.
   Viktor Kuncak, 16 July 2004.

   Updated with some QFBAPA util function in February 2007, vkuncak.
   Updated with prenex computation in Februrary 2011, Alexander Malkis.
*)

(*
 * Copyright (C) 2004 Viktor Kuncak <vkuncak@mit.edu>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the  Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307,
 * USA.
 *)

(* -------------------------------------------------- *)
(** Datatype of formulas *)

type ident = string

type binder = | Forallset | Existsset 
              | Forallint | Existsint 
              | Forallnat | Existsnat
	      | ForallProp | ExistsProp

type form = 
  | PropVar of ident
  | True
  | False
  | Not of form
  | And of form list
  | Or of form list
  | Impl of form * form
  | Bind of binder * ident * form
  | Less of intTerm * intTerm
  | Leq of intTerm * intTerm
  | Inteq of intTerm * intTerm
  | Seteq of setTerm * setTerm
  | Subseteq of setTerm * setTerm
and intTerm =
  | Intvar of ident
  | Const of int
  | Plus of intTerm list
  | Minus of intTerm * intTerm
  | Times of int * intTerm
  | IfThenElse of form * intTerm * intTerm
  | Div of intTerm * int
  | Card of setTerm
and setTerm =
  | Setvar of ident
  | Emptyset
  | Fullset
  | Complement of setTerm
  | Union of setTerm list
  | Inter of setTerm list

let maxcard = "MAXC"

(* -------------------------------------------------- *)
(**  Algorithm \alpha *)

  (* replace Seteq and Subseteq with Card(...)=0 *)
let simplify_set_relations (f:form) : form = 
  let rec sform f = match f with
  | PropVar _ -> f
  | False -> f
  | True -> f
  | Not f -> Not (sform f)
  | And fs -> And (List.map sform fs)
  | Or fs -> Or (List.map sform fs)
  | Impl(f1,f2) -> Impl(sform f1,sform f2)
  | Bind(b,id,f1) -> Bind(b,id,sform f1)
  | Less(it1,it2) -> Less(siterm it1, siterm it2)
  | Leq(it1,it2) -> Leq(siterm it1, siterm it2)
  | Inteq(it1,it2) -> Inteq(siterm it1,siterm it2)
  | Seteq(st1,st2) -> And[sform (Subseteq(st1,st2)); 
                          sform (Subseteq(st2,st1))]
  | Subseteq(st1,st2) -> Inteq(Card(Inter[st1;Complement st2]),Const 0)
  and siterm it = match it with
  | Intvar _ -> it
  | Const _ -> it
  | Plus its -> Plus (List.map siterm its)
  | Minus(it1,it2) -> Minus(siterm it1, siterm it2)
  | Times(k,it1) -> Times(k,siterm it1)
  | Div(it1,k) -> Div(siterm it1, k)
  | Card st -> it
  | IfThenElse(f1,it1,it2) -> 
      IfThenElse(sform f1, siterm it1, siterm it2)
  in sform f

  (* split f into quantifier sequence and body *)
let split_quants_body f = 
  let rec vl f acc = match f with
  | Bind(b,id,f1) -> vl f1 ((b,id)::acc)
  | f -> (acc,f)
  in vl f []

  (* extract set variables from quantifier sequence *)
let extract_set_vars quants = 
  List.map (fun (b,id) -> id)
    (List.filter (fun (b,id) -> (b=Forallset || b = Existsset))
       quants)

type partition = (ident * setTerm) list

  (* make canonical name for integer variable naming a cube *)
let make_name sts = 
  let rec mk sts = match sts with
  | [] -> ""
  | (Setvar _)::sts1 -> "1" ^ mk sts1
  | (Complement (Setvar _))::sts1 -> "0" ^ mk sts1
  | _ -> failwith "make_name: unexpected partition form"
  in "l_" ^ mk sts

  (* make all cubes over vs *)
let generate_partition (vs : ident list) : partition = 
  let add id ss = (Setvar id)::ss in
  let addc id ss = Complement (Setvar id)::ss in
  let add_set id inters =
    List.map (add id) inters @ 
    List.map (addc id) inters in 
  let mk_nm is = (make_name is, Inter is) in
  List.map mk_nm 
    (List.map List.rev
       (List.fold_right add_set vs [[]]))

  (* is the set term true in the set valuation
     -- reduces to propositional reasoning *)
let istrue (st:setTerm) (id,ivaluation) : bool = 
  let valuation = match ivaluation with
  | Inter v -> v
  | _ -> failwith "wrong valuation" in
  let lookup v = 
    if List.mem (Setvar v) valuation then true
    else if List.mem (Complement (Setvar v)) valuation then false
    else failwith ("istrue: unbound variable " ^ v ^ " in valuation") in
  let rec check st = match st with
  | Setvar v -> lookup v
  | Emptyset -> false
  | Fullset -> true
  | Complement st1 -> not (check st1)
  | Union sts -> List.fold_right (fun st1 t -> check st1 || t) sts false
  | Inter sts -> List.fold_right (fun st1 t -> check st1 && t) sts true
  in check st

  (* compute cardinality of set expression 
     as a sum of cardinalities of cubes *)
let get_sum (p:partition) (st:setTerm) : intTerm list = 
  List.map (fun (id,inter) -> Intvar id)
    (List.filter (istrue st) p)

  (* replace cardinalities of sets with sums of 
     variables denoting cube cardinalities *)
let replace_cards (p:partition) (f:form) : form = 
  let rec repl f = match f with
  | PropVar _ -> f
  | False -> False 
  | True -> True
  | Not f -> Not (repl f)
  | And fs -> And (List.map repl fs)
  | Or fs -> Or (List.map repl fs)
  | Impl(f1,f2) -> Impl(repl f1,repl f2)
  | Bind(b,id,f1) -> Bind(b,id,repl f1)
  | Less(it1,it2) -> Less(irepl it1,irepl it2)
  | Leq(it1,it2) -> Leq(irepl it1,irepl it2)
  | Inteq(it1,it2) -> Inteq(irepl it1,irepl it2)
  | Seteq(_,_)|Subseteq(_,_) -> failwith "failed inv in replace_cards"
  and irepl it = match it with
  | Intvar _ -> it
  | Const _ -> it
  | Plus its -> Plus (List.map irepl its)
  | Minus(it1,it2) -> Minus(irepl it1, irepl it2)
  | Times(k,it1) -> Times(k, irepl it1)
  | Div(it1, k) -> Div(irepl it1, k)
  | Card st -> Plus (get_sum p st)
  | IfThenElse(f1,it1,it2) -> IfThenElse(repl f1, irepl it1, irepl it2)
  in repl f

let apply_quants quants f =
  List.fold_right (fun (b,id) f -> Bind(b,id,f)) quants f

let make_defining_eqns id part = 
  let rec mk ps = match ps with
  | [] -> []
  | (id1,Inter (st1::sts1)) :: (id2,Inter (st2::sts2)) :: ps1
    when (st1=Setvar id && st2=Complement (Setvar id) && sts1=sts2) ->
      (Inter sts1,make_name sts1,id1,id2) :: mk ps1
  | _ -> failwith "make_triples: unexpected partition form" in
  let rename_last lss = match lss with
  | [(s,l,l1,l2)] -> [(s,maxcard,l1,l2)]
  | _ -> lss in
  rename_last (mk part)

  (* -------------------------- *)
  (* main loop of the algorithm *)
  (* -------------------------- *)
let rec eliminate_all quants part gr = match quants with
  | [] -> gr
  | (ExistsProp,id)::quants1 ->
      eliminate_all quants1 part (Bind(ExistsProp,id,gr))
  | (ForallProp,id)::quants1 ->
      eliminate_all quants1 part (Bind(ForallProp,id,gr))
  | (Forallint,id)::quants1 ->
      eliminate_all quants1 part (Bind(Forallint,id,gr))
  | (Existsint,id)::quants1 ->
      eliminate_all quants1 part (Bind(Existsint,id,gr))
  | (Existsnat,id)::quants1 ->
      eliminate_all quants1 part (Bind(Existsnat,id,gr))
  | (Forallnat,id)::quants1 ->
      eliminate_all quants1 part (Bind(Forallnat,id,gr))
  | (Existsset,id)::quants1 ->
      let eqns = make_defining_eqns id part in
      let newpart = List.map (fun (s,l',_,_) -> (l',s)) eqns in 
      let mk_conj (_,l',l1,l2) = Inteq(Intvar l',Plus[Intvar l1;Intvar l2]) in
      let conjs = List.map mk_conj eqns in
      let lquants = List.map (fun (l,_) -> (Existsnat,l)) part in
      let gr1 = apply_quants lquants (And (conjs @ [gr])) in
      eliminate_all quants1 newpart gr1
  | (Forallset,id)::quants1 ->
      let eqns = make_defining_eqns id part in
      let newpart = List.map (fun (s,l',_,_) -> (l',s)) eqns in 
      let mk_conj (_,l',l1,l2) = Inteq(Intvar l',Plus[Intvar l1;Intvar l2]) in
      let conjs = List.map mk_conj eqns in
      let lquants = List.map (fun (l,_) -> (Forallnat,l)) part in
      let gr1 = apply_quants lquants (Impl(And conjs, gr)) in
      eliminate_all quants1 newpart gr1

(* ------------------------- *)
(* Added by Alexander Malkis *)
(* Optimizing computation of prenex normal form. *)
module SetOfIdentifiers = Set.Make(String)
type setOfIdentifiers = SetOfIdentifiers.t

(* returns free variables of a term or a formula *)
let rec free_var_intTerm (t:intTerm):setOfIdentifiers=
  (match t with
      Intvar x -> SetOfIdentifiers.singleton x
    | Const _ | Plus [] -> SetOfIdentifiers.empty
    | Plus (g::gs) -> SetOfIdentifiers.union (free_var_intTerm g) (free_var_intTerm (Plus gs))
    | Minus (g1,g2) -> SetOfIdentifiers.union (free_var_intTerm g1) (free_var_intTerm g2)
    | Times (_,g) -> free_var_intTerm g
    | IfThenElse (f,t1,t2) -> SetOfIdentifiers.union (free_var_form f) (SetOfIdentifiers.union (free_var_intTerm t1) (free_var_intTerm t2))
    | Div (t1,_) -> free_var_intTerm t1
    | Card s -> free_var_setTerm s
  )
and free_var_form (f:form) : setOfIdentifiers =
  (match f with 
      PropVar x -> SetOfIdentifiers.singleton x
    | Not g -> free_var_form g
    | True | False -> SetOfIdentifiers.empty
    | And gs | Or gs -> free_var_form_list gs
    | Impl (g1,g2) ->SetOfIdentifiers.union (free_var_form g1) (free_var_form g2)
    | Bind (b,x,g) -> SetOfIdentifiers.remove x (free_var_form g)
    | Less (g1,g2) | Leq(g1,g2) | Inteq (g1,g2) -> SetOfIdentifiers.union (free_var_intTerm g1) (free_var_intTerm g2)
    | Seteq (g1,g2) | Subseteq(g1,g2) -> SetOfIdentifiers.union (free_var_setTerm g1) (free_var_setTerm g2)
  )
and free_var_setTerm (s:setTerm) : setOfIdentifiers =
  (match s with 
      Setvar x -> SetOfIdentifiers.singleton x
    | Emptyset| Fullset -> SetOfIdentifiers.empty
    | Complement s1 -> free_var_setTerm s1
    | Union ss | Inter ss -> List.fold_left (fun sofar s1 -> SetOfIdentifiers.union (free_var_setTerm s1) sofar) SetOfIdentifiers.empty ss
  )
and free_var_form_list (fs: form list) = List.fold_left (fun sofar g -> SetOfIdentifiers.union (free_var_form g) sofar) SetOfIdentifiers.empty fs

(* [subst_form f new old] substitutes free occurences of old by new in f *)
let subst_form (f:form) (new_id:ident) (old_id:ident) =
  let rec s_form (f:form)=
    (match f with
	PropVar x -> if x=old_id then PropVar new_id else f
      | True | False -> f
      | Not g -> Not (s_form g)
      | And gs -> And (List.rev_map s_form gs)
      | Or gs -> Or (List.rev_map s_form gs)
      | Impl (g1,g2) -> Impl ((s_form g1),(s_form g2))
      | Bind (b,x,g) -> if x=old_id then f else Bind (b,x,(s_form g))
      | Less (i1,i2) -> Less ((s_intTerm i1),(s_intTerm i2))
      | Leq (i1,i2) -> Leq ((s_intTerm i1),(s_intTerm i2))
      | Inteq (i1,i2) -> Inteq ((s_intTerm i1),(s_intTerm i2))
      | Seteq (s1,s2) -> Seteq ((s_setTerm s1),(s_setTerm s2))
      | Subseteq (s1,s2) -> Subseteq ((s_setTerm s1),(s_setTerm s2))
    )
  and s_intTerm (t:intTerm)=
  (match t with
      Intvar x -> if x=old_id then Intvar new_id else t
    | Const _ -> t
    | Plus ts -> Plus (List.rev_map s_intTerm ts)
    | Minus (i1,i2) -> Minus ((s_intTerm i1),(s_intTerm i2))
    | Times (i,i1) -> Times(i,(s_intTerm i1))
    | IfThenElse (f,i1,i2) -> IfThenElse ((s_form f),(s_intTerm i1),(s_intTerm i2))
    | Div (it,i) -> Div ((s_intTerm it),i)
    | Card s -> Card (s_setTerm s)
  )
  and s_setTerm (s:setTerm) =
    (match s with
	Setvar x -> if x=old_id then Setvar new_id else s
      | Emptyset |Fullset ->s
      | Complement s1 -> Complement (s_setTerm s1)
      | Union ss -> Union (List.rev_map s_setTerm ss)
      | Inter ss -> Inter (List.rev_map s_setTerm ss)
    )
  in s_form f

(* prenex f
   Returns a prenex normal form of a formula f. Assumes that the condition of IfThenElse does not contain quantifiers. *)
let rec prenex (f:form) =
  (* dualizes a quantifier *)
  let dual = function
      Existsset -> Forallset
    | Existsint -> Forallint
    | Existsnat -> Forallnat
    | ExistsProp -> ForallProp
    | Forallset -> Existsset
    | Forallint -> Existsint
    | Forallnat -> Existsnat
    | ForallProp -> ExistsProp
  in
  (* [move_not_inwards f] takes a formula f in prenext normal form, i.e.
     Q1xq Q2x2 ... Qnxn g where Q1,...,Qn are quantifiers, x1,...,xn are variables and g is quantifier-free.
     Returns the formula Q1'xq Q2'x2 ... Qn'xn (simplification of (not g)) where Forall'=Exists and Exists'=Forall.
  *)
  let rec move_not_inwards (f:form) =
    (match f with
        PropVar _ -> (Not f)
      | True -> False
      | False -> True
      | Not g -> g
      | And [] -> False (* Not (And over the empty set) = Not (True) = False *)
      | And [(Not h)] -> h
      | And [h] -> Not h
      | And hs -> Not f
      | Or [] -> True (* Not (Or over the empty set) = Not (False) = True *)
      | Or [(Not h)] -> h
      | Or hs -> Not (Or hs)
      | Impl (True,h2) -> move_not_inwards h2
      | Impl (False,_) -> False (* Not (Not=>...) = Not True = False *)
      | Impl (h1,True) -> False
      | Impl (h1,False) -> h1 (* Not (h1=>False) = Not (Not h1) = h1 *)
      | Impl (h1,(Not h2)) -> And [h1;h2] (* Not (h1=>(Not h2)) = Not ((Not h1) Or (Not h2)) = h1 And h2 *)
      | Impl (h1,h2) -> And [h1;Not h2]  (* Not (h1=>h2) = Not ((Not h1) Or h2) = h1 And (Not h2) *)
      | Bind (b,v,g) -> Bind ((dual b),v,(move_not_inwards g))
      | Less (g1,g2) -> Leq(g2,g1)
      | Leq (g1,g2) -> Less(g2,g1)
      | Inteq (g1,g2) -> if g1=g2 then False else Not f
      | Seteq (g1,g2) -> if g1=g2 then False else Not f
      | Subseteq (g1,g2) -> if g1=g2 then False else Not f)
  in
  (* Computes union over the second components of a list. *)
  let bigunion_ident_list2 lst =
    let rec bigunion_ident_list2_aux sofar lst= 
      (match lst with
	  [] -> sofar
	| l::ls -> bigunion_ident_list2_aux (SetOfIdentifiers.union (snd l) sofar) ls
      )
    in bigunion_ident_list2_aux SetOfIdentifiers.empty lst
  in
  (* Takes a list of quantified formulas fs with quantifiers outside and a list of some formulas gs.
     Among all variables bound by the outermost quantifers in fs, try to find one which does not occur free in all other formulas of fs or gs.
     Return Some v if such v is found, otherwise return None. *)
  let find_var_free_only_in_one_formula (fs:form list) (gs:form list) =
    let list_of_pairs_v_fv_of_fs = List.rev_map (fun elem ->
      (match elem with
	  Bind(_,v,body) -> (v,(free_var_form elem))
	| _ -> raise (Failure "prenex: find_var_free_only_in_one_formula applied to a list containing a non-binder")
      )
    ) fs in
    let rec scan (before_set:setOfIdentifiers) (x,fvs) after_lst =
      let before_and_after_set = SetOfIdentifiers.union before_set (bigunion_ident_list2 after_lst)
      in if SetOfIdentifiers.mem x before_and_after_set 
	then (match after_lst with
	    [] -> None
	  | a::alst -> scan (SetOfIdentifiers.union fvs before_set) a alst)
	else Some x
    in (match list_of_pairs_v_fv_of_fs with
	[] -> raise (Failure "prenex: find_var_free_only_in_one_formula applied to an empty list")
      | f::ffs -> scan (free_var_form_list gs) f ffs)
  in
  (* Takes a map h, a quantified formula f with a quantifier outside, a list of formulas fs.
     Returns a formula starting with the quantifer of f and the body being h applied to the body of f appended by the remaining list *)
  let put_quantifier_outside (h:(form list -> form)) (b,v,body) (fs:form list) :form =
    let fv_of_remainder = free_var_form_list fs in
    if SetOfIdentifiers.mem v fv_of_remainder
    then let new_v = Util.fresh_name v in
	 let new_body = subst_form body new_v v in
	 Bind(b,new_v,(h (new_body::fs)))
    else Bind(b,v,(h (body::fs)))
  in
  (* Takes a map h, two quantified formulas f and g with a quantifier outside of f. 
     Returns a formula starting with the dual quantifier of f and the body being h applied to the body of f and g.
  *)
  let put_dual_of_first_quantifier_outside (h: form -> form -> form) (b,v,body) (g:form) : form =
    if SetOfIdentifiers.mem v (free_var_form g) 
    then let new_v=Util.fresh_name v in
	 let new_body=subst_form body new_v v in
	 Bind((dual b),new_v,(h new_body g))
    else Bind((dual b),v,(h body g))
  in
  (* Takes a map h, two quantified formulas f and g with a quantifier outside of g.
     Returns a formula starting with the quantifier of g and the body being h applied to f and the body of g.
  *)
  let put_second_quantifier_outside (h:form->form->form) (f:form) (b,v,body) : form =
    if SetOfIdentifiers.mem v (free_var_form f)
    then let new_v=Util.fresh_name v in
	 let new_body=subst_form body new_v v in
	 Bind(b,new_v,(h f new_body))
    else Bind(b,v,(h f body))
  in
  (* Takes a list of quantified formulas fs where the outermost quantifer is the same b, a map h and a list of some formulas rest. Returns a formula starting with b and the body being h applied to the concatenation of the bodies of fs and rest. *)
  let combine_quantifiers (h:(form list->form)) (b:binder) (fs:form list) (rest:form list) :form =
    (match fs with
	(Bind(_,v,_))::ffs -> (
	  let new_v=(match find_var_free_only_in_one_formula fs rest with 
	      None -> Util.fresh_name v
	    | Some x -> x) in 
	  let list_of_fs_bodies= List.rev_map (fun elem ->
	    (match elem with
		Bind(_,v,g) -> subst_form g new_v v
	      | _ -> raise (Failure "prenex: combine_quantifiers expects a binder")
	    )) fs in
	  Bind (b,new_v,(h (List.rev_append list_of_fs_bodies rest))))
      | _ -> raise (Failure "prenex: combine_quantifiers cannot combine an empty list or a list containing non-quantified formulas"))
  in
  (* Takes a map h, two quantified formulas f and g where f is universally quantified and g is existentially quantified.
     Returns an existentially quantified formula where the body is h applied to the bodies of f and g.
  *)
  let combine_quantifiers2 (h:form->form->form) (bf,vf,bodyf) (bg,vg,bodyg) =
    let new_v=(if vf=vg then vf else
	if SetOfIdentifiers.mem vf (free_var_form bodyg) then
	  if SetOfIdentifiers.mem vg (free_var_form bodyf) then Util.fresh_name vf else vg
	else vf
    ) in 
    let new_bodyf = subst_form bodyf new_v vf in
    let new_bodyg = subst_form bodyg new_v vg in
    Bind(bg,new_v,(h new_bodyf new_bodyg))
  in
  (* [move_and_inwards fs] takes a list of formulas in prenex normal form and computes the prenex normal form of their conjunction. Combines quantifiers (ALL x. f) & (ALL y. g) into (ALL x_new. f & g[x_new/y]) where x_new is fresh or (x_new=x and x doesn't occur in y). *) 
  let rec move_and_inwards (fs:form list):form =
    let fs=List.fold_left (fun sofar f -> 
      (match sofar with
	  [False] -> [False]
	| _ -> (match f with True -> sofar | False -> [False] | _ -> (f::sofar))
      )) [] fs in
    let put_quantifier_outside_and = put_quantifier_outside move_and_inwards in
    let combine_quantifiers_and = combine_quantifiers move_and_inwards in
    (match fs with
         []->True
       | [h] -> h
       | _ ->
	 let (starts_with_forallset,starts_not_with_forallset)=List.partition (function Bind(Forallset,_,_)->true | _ ->false) fs in
	 (match starts_with_forallset with
	     [] -> let (starts_with_forallint,starts_not_with_forallset_or_forallint)=List.partition (function Bind(Forallint,_,_)->true | _ ->false) starts_not_with_forallset in
		   (match starts_with_forallint with
		       [] -> let (starts_with_forallnat,starts_not_with_forallset_or_forallint_or_forallnat)=List.partition (function Bind(Forallnat,_,_)->true | _ ->false) starts_not_with_forallset_or_forallint in
			     (match starts_with_forallnat with
				 [] -> let (starts_with_forallprop,starts_not_with_forall)=List.partition (function Bind(ForallProp,_,_)->true | _ ->false) starts_not_with_forallset_or_forallint_or_forallnat in 
				       (match starts_with_forallprop with
					   [] -> let (starts_with_exists,rest)=List.partition (function Bind(Existsset,_,_)|Bind(Existsint,_,_)|Bind(Existsnat,_,_)|Bind(ExistsProp,_,_) -> true | _-> false) starts_not_with_forall in 
						 (match starts_with_exists with
						     [] -> And rest (* nothing starts with forall and nothing starts with exists *)
						   | (Bind (b,v,body))::gs -> put_quantifier_outside_and (b,v,body) (List.rev_append rest gs)
						   | _ -> raise (Failure "prenex: move_and_inwards doesn't work: existential quantifier expected")
						 )
					 | [Bind (b,v,body)] -> put_quantifier_outside_and (b,v,body) starts_not_with_forall
					 | _ -> combine_quantifiers_and ForallProp starts_with_forallprop starts_not_with_forall
				       )
			       |  [Bind (b,v,body)] -> put_quantifier_outside_and (b,v,body) starts_not_with_forallset_or_forallint_or_forallnat
			       | _-> combine_quantifiers_and Forallnat starts_with_forallnat starts_not_with_forallset_or_forallint_or_forallnat
			     )
		     | [Bind (b,v,body)] -> put_quantifier_outside_and (b,v,body) starts_not_with_forallset_or_forallint
		     | _ -> combine_quantifiers_and Forallint starts_with_forallint starts_not_with_forallset_or_forallint
		   )
	   | [Bind (b,v,body)] -> put_quantifier_outside_and (b,v,body) starts_not_with_forallset
           | _ -> combine_quantifiers_and Forallset starts_with_forallset starts_not_with_forallset
	 )
    )
  in 
  (* [move_or_inwards fs] takes a list of formulas in prenex normal form and computes the prenex normal form of their disjunction. Combines quantifiers (EX x. f) || (EX y. g) into (EX x_new. f || g[x_new/y]) where x_new is fresh or (x_new=x and x doesn't occur in y). *) 
  let rec move_or_inwards (fs:form list) : form =
    let fs=List.fold_left (fun sofar f -> 
      (match sofar with
	  [True] -> [True]
	| _ -> (match f with False -> sofar | True -> [True] | _ -> (f::sofar))
      )) [] fs in
    let put_quantifier_outside_or = put_quantifier_outside move_or_inwards in
    let combine_quantifiers_or = combine_quantifiers move_or_inwards in
    (match fs with
	[] -> False
      | [h] -> h
      | _ ->
	let (starts_with_existsset,starts_not_with_existsset) = List.partition (function | Bind(Existsset,_,_) -> true | _ -> false) fs in
	(match starts_with_existsset with
	    [] -> let (starts_with_existsint,starts_not_with_existsset_or_existsint) = List.partition (function | Bind(Existsint,_,_) -> true | _ -> false) starts_not_with_existsset in
		  (match starts_with_existsint with
		      [] -> let (starts_with_existsnat,starts_not_with_existsset_or_existsint_or_existsnat) = List.partition (function | Bind(Existsnat,_,_) -> true | _ -> false) starts_not_with_existsset_or_existsint in
			    (match starts_with_existsnat with
				[] -> let (starts_with_existsprop,starts_not_with_exists) = List.partition (function | Bind(ExistsProp,_,_) -> true | _ -> false) starts_not_with_existsset_or_existsint_or_existsnat in
				      (match starts_with_existsprop with
					  [] -> let (starts_with_forall,starts_not_with_quantifier) =  List.partition (function | Bind(Forallset,_,_)| Bind(Forallint,_,_)| Bind(Forallnat,_,_)| Bind(ForallProp,_,_) -> true | _ -> false) starts_not_with_exists in
						(match starts_with_forall with
						    [] -> Or starts_not_with_quantifier
						  | (Bind (b,v,body))::gs -> put_quantifier_outside_or (b,v,body) (List.rev_append gs starts_not_with_quantifier)
						  | _ -> raise (Failure "prenex: move_or_inwards doesn't work: universal quantifier expected")
						)
					| [Bind (b,v,body)] -> put_quantifier_outside_or (b,v,body) starts_not_with_exists
					| _ -> combine_quantifiers_or ExistsProp starts_with_existsprop starts_not_with_exists
				      )
			      | [Bind (b,v,body)] ->put_quantifier_outside_or (b,v,body) starts_not_with_existsset_or_existsint_or_existsnat
			      | _ -> combine_quantifiers_or Existsnat starts_with_existsnat starts_not_with_existsset_or_existsint_or_existsnat
			    )
		    | [Bind (b,v,body)] -> put_quantifier_outside_or (b,v,body) starts_not_with_existsset_or_existsint
		    | _ -> combine_quantifiers_or Existsint starts_with_existsint starts_not_with_existsset_or_existsint
		  )
	  | [Bind (b,v,body)] -> put_quantifier_outside_or (b,v,body) starts_not_with_existsset
	  | _ -> combine_quantifiers_or Existsset starts_with_existsset starts_not_with_existsset
	)
    )
  in
  (* [move_impl_inwards f g] takes formulas f and g in prenex normal form and computes the prenex normal form of (f=>g).
     Combines (ALL x. h1)=>(EX y. h2) into (EX z. h1[z/x]=>h2[z/y]) where z=x if x=y or if x is not free in h2, z=y if x=y or y is not free in h1, z is fresh if x occurs free in h2 and y occurs free in h1. *)
  let rec move_impl_inwards (f:form) (g:form) : form =  
    let put_dual_of_first_quantifier_outside_impl triple = put_dual_of_first_quantifier_outside move_impl_inwards triple g in
    match f with
	True -> g
      | False -> True
      | Bind(bf,vf,bodyf) -> 
	(match g with
	    True -> True
	  | False -> move_not_inwards f
	  | Bind (bg,vg,bodyg) -> if (bf=Forallset || bf=Forallint || bf=Forallnat || bf=ForallProp) & (bf=(dual bg))
	    then combine_quantifiers2 move_impl_inwards (bf,vf,bodyf) (bg,vg,bodyg)
	    else put_dual_of_first_quantifier_outside_impl (bf,vf,bodyf)
	  | _ -> put_dual_of_first_quantifier_outside_impl (bf,vf,bodyf))
      | _ -> (match g with
	  True -> True
	  | False -> move_not_inwards f
	  | Bind(bg,vg,bodyg) ->put_second_quantifier_outside move_impl_inwards f (bg,vg,bodyg)
	  | _ -> Impl (f,g))
  in 
  (match f with
      PropVar _ | True | False -> f
    | Not f -> move_not_inwards (prenex f)
    | And lst -> move_and_inwards (List.rev_map prenex lst)
    | Or lst -> move_or_inwards (List.rev_map prenex lst)
    | Impl (f,g) -> move_impl_inwards (prenex f) (prenex g)
    | Bind (b,v,body) -> let pb = prenex body in if SetOfIdentifiers.mem v (free_var_form pb) then Bind(b,v,pb) else pb
    | _ -> f
  )
(* end of prenex computation *)
(* ------------------------- *)

(* ************************************************************
   Pretty printing 
 ************************************************************)

let string_of_form (f:form) : string = 
  let p s = "(" ^ s ^ ")" in
  let rec str f = match f with
  | PropVar id -> theid id
  | False -> "False"
  | True -> "True"
  | Not f1 -> "\\lnot " ^ str f1
  | And [] -> "\\btrue"
  | And fs -> ninfix "\\land" (List.map str fs)
  | Or [] -> "\\btrue"
  | Or fs -> ninfix "\\lor" (List.map str fs)
  | Impl(f1,f2) -> infix (str f1) "\\implies" (str f2)
  | Bind(Forallset,id,f1) -> binder "\\forallset" id f1
  | Bind(Existsset,id,f1) -> binder "\\existsset" id f1
  | Bind(Forallint,id,f1) -> binder "\\forallint" id f1
  | Bind(Existsint,id,f1) -> binder "\\existsint" id f1
  | Bind(Forallnat,id,f1) -> binder "\\forallnat" id f1
  | Bind(Existsnat,id,f1) -> binder "\\existsnat" id f1
  | Bind(ForallProp,id,f1) -> binder "\\forallprop" id f1
  | Bind(ExistsProp,id,f1) -> binder "\\existsprop" id f1
  | Less(it1,it2) -> infix (istr it1) "<" (istr it2)
  | Leq(it1,it2) -> infix (istr it1) "\\leq" (istr it2)
  | Inteq(it1,it2) -> infix (istr it1) "=" (istr it2)
  | Seteq(st1,st2) -> infix (sstr st1) "\\<seteq>" (sstr st2)
  | Subseteq(st1,st2) -> infix (sstr st1) "\\subseteq" (sstr st2)
  and istr it = match it with
  | Intvar id -> theid id
  | Const c -> theint c
  | Plus its -> ninfix "+" (List.map istr its)
  | Minus(it1,it2) -> infix (istr it1) "-" (istr it2)
  | Times(k,it) -> infix (theint k) "*" (istr it)
  | Div(it,k) -> infix (istr it) "div" (theint k)
  | Card st -> "|" ^ sstr st ^ "|"
  | IfThenElse(f1,it1,it2) ->
    p ("if " ^ p (str f1) ^ " then " ^ istr it1 ^ " else " ^ istr it2)
  and sstr st = match st with
  | Setvar id -> theid id
  | Emptyset -> "\\emptyset"
  | Fullset -> "\\Univ"
  | Complement st -> "({" ^ sstr st ^ "})^c"
  | Union sts -> ninfix "\\cup" (List.map sstr sts)
  | Inter sts -> ninfix "\\cap" (List.map sstr sts)
  and ninfix op ss = p (String.concat (" " ^ op ^ " ") ss)
  and infix s1 op s2 = p (s1 ^ " " ^ op ^ " " ^ s2)
  and binder b id f = b ^ " " ^ theid id ^ ". " ^ str f
  and theint k = Printf.sprintf "%d" k
  and theid s = 
    let sf s = if String.length s > 1 then "\\mathit{" ^ s ^ "}" else s in
    try 
      let i = String.index s '_' in
      sf (String.sub s 0 i) ^ "_{" ^
      String.sub s (i+1) (String.length s - i - 1) ^ "}"
    with Not_found -> sf s
  in str f

(* putting everything together *)

(* Assumes that in f the subformulas if-then-else don't contain quantifiers in the condition. *)
let alpha (f:form) : form =
  (* let _=Util.msg ("alpha started on\n"^(string_of_form f)^"\n") in *)
  let g= prenex f in
  (* let _= Util.msg ("prenex computation finished with\n"^(string_of_form g)^"\n") in *)
  let (quants,fm) = split_quants_body g in
  let fm1 = simplify_set_relations fm in
  let setvars = List.rev (extract_set_vars quants) in
  let part = generate_partition setvars in
  let g1 = replace_cards part fm1 in
  eliminate_all quants part g1

(* additional stuff *)

(** set variables in a formula *)
let set_vars_of (f : form) : ident list = 
  let rec fv (bv : ident list) (f : form) : ident list =
    match f with
      | PropVar _ -> []
      | False -> []
      | True -> []
      | Not f1 -> fv bv f1
      | And fs -> List.concat (List.map (fv bv) fs)
      | Or fs -> List.concat (List.map (fv bv) fs)
      | Impl(f1,f2) -> fv bv f1 @ fv bv f2
      | Bind(b,v,f1) -> fv (v::bv) f1
      | Less(it1,it2)
      | Leq(it1,it2)
      | Inteq(it1,it2) -> fvi bv it1 @ fvi bv it2
      | Seteq(st1,st2)
      | Subseteq(st1,st2) -> fvs bv st1 @ fvs bv st2
  and fvi bv it = match it with
    | Intvar _ -> []
    | Const c -> []
    | Plus its -> List.concat (List.map (fvi bv) its)
    | Minus(it1,it2) -> fvi bv it1 @ fvi bv it2
    | Times(k,it) -> fvi bv it
    | Div(it,k) -> fvi bv it
    | Card st -> fvs bv st
    | IfThenElse(f1,it1,it2) -> 
	fv bv f1 @ fvi bv it1 @ fvi bv it2
  and fvs bv st = match st with
    | Setvar id -> if List.mem id bv then [] else [id]
    | Emptyset -> []
    | Fullset -> []
    | Complement st -> fvs bv st
    | Union sts -> List.concat (List.map (fvs bv) sts)
    | Inter sts -> List.concat (List.map (fvs bv) sts)
  in
    Util.remove_dups (fv [] f)

let flip_binder (b : binder) : binder = match b with
  | Forallset -> Existsset
  | Existsset -> Forallset
  | Forallint -> Existsint
  | Existsint -> Forallint
  | Forallnat -> Existsnat
  | Existsnat -> Forallnat
  | ForallProp -> ExistsProp
  | ExistsProp -> ForallProp
let universal_binder (b : binder) : bool = match b with
  | ExistsProp
  | Existsset
  | Existsint
  | Existsnat -> false
  | ForallProp
  | Forallset
  | Forallint
  | Forallnat -> true

(** negation-normal form - ignoring formulas inside IfThenElse *)
let negation_normal_form (f0 : form) : form =
  let apply_pos (pos : bool) (f : form) : form =
    if pos then f else Not f in
  let rec nnf (pos : bool) (f : form) : form =
    match f with
      | PropVar _ 
      | True
      | False
      | Less(_,_)
      | Leq(_,_)
      | Inteq(_,_)
      | Seteq(_,_)
      | Subseteq(_,_) 
	  (* base cases *)
	-> apply_pos pos f
      | Not f1 -> nnf (not pos) f1
      | And fs -> 
	  if pos then And (List.map (nnf pos) fs)
	  else Or (List.map (nnf pos) fs)
      | Or fs -> 
	  if pos then Or (List.map (nnf pos) fs)
	  else And (List.map (nnf pos) fs)
      | Impl(f1,f2) -> nnf pos (Or [Not f1;f2])
      | Bind(b,id,f1) -> 
	  if pos then Bind(b,id,nnf pos f1)
	  else Bind(flip_binder b,id,nnf pos f1)
  in
    nnf true f0

exception NotQF of form
(** If f has only universal quantifiers, return a quantifier-free formula
    (since we are checking validity),
    otherwise return None *)
let get_quantifier_free (f : form) : form option =
  (* pre: f is in nnf *)
  let rec get_qf (f : form) : form =
    match f with
      | PropVar _ 
      | True
      | False
      | Less(_,_)
      | Leq(_,_)
      | Inteq(_,_)
      | Seteq(_,_)
      | Subseteq(_,_) -> 
	  f
      | Not f1 -> Not (get_qf f1)
      | And fs -> And (List.map get_qf fs)
      | Or fs -> Or (List.map get_qf fs)
      | Impl(f1,f2) -> get_qf (Or [Not f1;f2])
      | Bind(b,id,f1) when universal_binder b -> 
	  get_qf f1
      | Bind(_,_,f1) -> 
	  raise (NotQF f)
  in
    try
      Some (get_qf f)
    with NotQF bf ->
      Util.msg ("\nBAPA formula not quantifier-free due to\n" ^
		  string_of_form bf);
      None

let approximate_quantifier_free (f0 : form) : form =
  let rec approx (f : form) : form =
    match f with
      | PropVar _ 
      | True
      | False
      | Less(_,_)
      | Leq(_,_)
      | Inteq(_,_)
      | Seteq(_,_)
      | Subseteq(_,_) -> 
	  f
      | Not f1 -> Not (approx f1)
      | And fs -> And (List.map approx fs)
      | Or fs -> Or (List.map approx fs)
      | Impl(f1,f2) -> approx (Or [Not f1;f2])
      | Bind(b,id,f1) when universal_binder b -> 
	  approx f1
      | Bind(_,_,f1) -> False
  in
    approx f0

(** compute formula size *)
let formula_size (f : form) : int =
  let rec sum (xs : int list) = 
    match xs with 
      | [] -> 0
      | x::xs -> x + sum xs in
  let rec fsize (f : form) : int =
    match f with
      | PropVar _ | True | False -> 1
      | Not f -> 1 + fsize f
      | And fs | Or fs -> List.length fs + sum (List.map fsize fs)
      | Impl(f1,f2) -> 1 + fsize f1 + fsize f2
      | Bind(_,_,f1) -> 1 + fsize f1
      | Inteq(i1,i2) | Less(i1,i2) | Leq(i1,i2) -> 1 + isize i1 + isize i2
      | Seteq(s1,s2) | Subseteq(s1,s2) -> 1 + ssize s1 + ssize s2
  and isize (i : intTerm) : int =
    match i with
      | Intvar _ | Const _ -> 1
      | Plus is -> List.length is + sum (List.map isize is)
      | Minus(i1,i2) -> 1 + isize i1 + isize i2
      | Times(_,i1) | Div(i1,_) -> 1 + isize i1
      | IfThenElse(f1,i1,i2) -> 1 + fsize f1 + isize i1 + isize i2
      | Card s -> 1 + ssize s
  and ssize (s : setTerm) : int =
    match s with
      | Setvar _ | Emptyset | Fullset -> 1
      | Complement s1 -> 1 + ssize s
      | Union ss | Inter ss -> List.length ss + sum (List.map ssize ss)
  in
    fsize f

(* ****** examples ********************)

(*
let add_partition_def part fm = 
  let mk_conj (id,inter) = Inteq(Intvar id,Card(inter)) in
  let conjs = List.map mk_conj part in
  let body = And (conjs @ [fm]) in
  let mk_quant (id,_) f = Bind(Existsset,id,f) in
  List.fold_right mk_quant part body
*)

let process (f:form) = begin 
  print_string "Input formula is:\n\n$";
  print_string (string_of_form f);
  let res = alpha f in
  print_string "$\n\nOutput formula is:\n\n$";
  print_string (string_of_form res);
  print_string "$\n";
  res
end

let e=Setvar "e" and content=Setvar "content" and 
    content'=Setvar "content'" 
and size=Intvar "size" and size'=Intvar "size'"

let a = Setvar "A" and b = Setvar "B"

let example1 =
  Bind(Forallset,"e",
  Bind(Forallset,"content", Bind(Forallset,"content'",
  Bind(Forallint,"size", Bind(Forallint,"size'",
    Impl(And [Inteq(Card(e),Const 1);
              Inteq(Card(Inter[e;content]),Const 0);
              Inteq(Card(content),size);
              Seteq(content',Union[content;e]);
              Inteq(size',Plus[size;Const 1])],
         And[Less(Const 0,size'); Inteq(Card(content'),size')])
  )))))

let example2 =
  Bind(Existsset,"e",
  Bind(Existsset,"content", Bind(Existsset,"content'",
  Bind(Existsint,"size", Bind(Existsint,"size'",
    And [Inteq(Card(e),Const 1);
         Inteq(Card(Inter[e;content]),Const 0);
         Inteq(Card(content),size);
         Seteq(content',Union[content;e]);
         Inteq(size',Plus[size;Const 1]);
         Not (And[Less(Const 0,size'); Inteq(Card(content'),size')])]
  )))))

let example3 =
  Bind(Forallset,"A",
       Bind(Forallset, "B",
	    Impl(Subseteq(a,b),Seteq(a,b))))

let example4 =
  Bind(Forallset,"A",
       Bind(Forallset, "B",
	    Impl(And([Subseteq(b,a); Subseteq(a,b)]),Seteq(a,b))))

let example5 =
  Bind(Forallnat, "x",
  Bind(Forallset,"A",
       Bind(Forallset, "B",
            And [Less (Intvar "x", Const 10);
	         Impl(And([Subseteq(b,a); Subseteq(a,b)]),Seteq(a,b))])))

let example6 =
  Bind(Existsnat, "x",
  Bind(Forallset,"A",
       Bind(Forallset, "B",
            And [Less (Intvar "x", Const 10);
	         Impl(And([Subseteq(b,a); Subseteq(a,b)]),Seteq(a,b))])))

let example7 =
  Bind(Forallnat, "x",
  Bind(Forallset,"A",
       Bind(Forallset, "B",
	         Impl(And[Less (Intvar "x", Const 10);
                          Subseteq(b,a); Subseteq(a,b)],
                      And[Seteq(a,b); Less(Intvar "x", Const 9)]))))

let example8 =
  Bind(Forallset,"A",
       Bind(Forallset, "B",
            And[Leq(Card a, Card (Union [a;b]));
                Leq(Card (Union [a;b]), Plus[Card a; Card b])]))

let example9 = Bind(Forallset,"A",Bind(Forallset,"Sing_t1",Bind(Forallnat,"count",Bind(Forallnat,"C",Bind(Forallset,"Sing_t3_17",Bind(Existsset,"Sing_t3",
  Impl (And([(Inteq ((Card (Setvar "Sing_t3")),(Const 1)));
	     (Inteq ((Card (Setvar "Sing_t1")),(Const 1)));
	     (Inteq ((Card (Setvar "Sing_t3_17")),(Const 1)));
             (Leq((Card (Setvar "A")),(Intvar "count")));
             (Impl((Subseteq ((Setvar "Sing_t3"),(Setvar "C"))),(Inteq ((Intvar "count"),(Const 0)))));
             (Subseteq ((Setvar "Sing_t3"),(Setvar "A")));
             (Subseteq ((Setvar "Sing_t3_17"),(Setvar "C")))]),
        False)
  ))))))


(*
let pa_example = process example9
*)

