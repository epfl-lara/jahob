(** Connvert BAPA formula in Presburger subset into Presburger formula ast
   (mostly just datatype conversion). - obsolete *)

open Alpha
open Presburger


let rec intTermToAExp (it : intTerm) : aExp = match it with
  | Intvar v -> Var v
  | Alpha.Const c -> Presburger.Const c
  | Plus its -> List.fold_left makePlus (Presburger.Const 0) its
  | Alpha.Minus (it1, it2) -> Presburger.Minus (intTermToAExp it1, intTermToAExp it2)
  | Times (c, it) -> Mult (c, intTermToAExp it)
  | Card _ -> failwith "Converting BAPA to Presburger: BAPA formula still contains Card"
  | _ -> failwith "Bapapres.intTermToAExp: construct to translate not supported yet"

and makePlus ae it = 
  let aeit = intTermToAExp it in
    Add (ae, aeit)

let rec occurs (i : ident) (bf : form) : bool = match bf with
  | Alpha.PropVar id -> i=id
  | Alpha.False
  | Alpha.True -> false
  | Alpha.Not f -> occurs i f
  | Alpha.And [] -> false
  | Alpha.And (f::fs) -> occurs i f || occurs i (Alpha.And fs)
  | Alpha.Or [] -> false
  | Alpha.Or (f::fs) -> occurs i f || occurs i (Alpha.And fs)
  | Impl (f1, f2) -> occurs i f1 || occurs i f2
  | Bind (b, i1, f) -> i1 <> i && occurs i f
  | Alpha.Less (it1, it2) 
  | Alpha.Leq (it1, it2)
  | Inteq (it1, it2) -> int_occurs i it1 || int_occurs i it2
  | Seteq(s1,s2) 
  | Subseteq(s1,s2) -> set_occurs i s1 || set_occurs i s2
  
and int_occurs (i : ident) (intt : intTerm) : bool = match intt with
  | Intvar i1 -> i1=i
  | Alpha.Const _ -> false
  | Alpha.Plus [] -> false
  | Alpha.Plus (i1::is) -> int_occurs i i1 || int_occurs i (Plus is)
  | Alpha.Minus (i1,i2) -> int_occurs i i1 || int_occurs i i2
  | Times (_,i1) -> int_occurs i i1
  | Div (i1,_) -> int_occurs i i1
  | Card s -> set_occurs i s
  | Alpha.IfThenElse(f1,i1,i2) -> occurs i f1 || int_occurs i i1 || int_occurs i i2
and set_occurs (i : ident) (sett : setTerm) : bool = match sett with
  | Setvar s -> i=s
  | Emptyset 
  | Fullset -> false
  | Complement s1 -> set_occurs i s1
  | Union [] -> false
  | Union (s1::setts1) -> set_occurs i s1 || set_occurs i (Union setts1)
  | Inter [] -> false
  | Inter (s1::setts1) -> set_occurs i s1 || set_occurs i (Inter setts1)

let rec bapaFormToPresForm (bapa : form) : presForm = match bapa with
  | Alpha.PropVar _ -> failwith "Bapapres: propvars not handled yet."
  | Alpha.False -> Presburger.presFormFalse
  | Alpha.True -> Presburger.presFormTrue
  | Alpha.Not f -> Presburger.Not (bapaFormToPresForm f)
  | Alpha.And fs -> 
      let h = bapaFormToPresForm (List.hd fs) in
	List.fold_left makeAnd h (List.tl fs)
  | Alpha.Or fs -> 
      let h = bapaFormToPresForm (List.hd fs) in
	List.fold_left makeOr h (List.tl fs)
(*
  | Alpha.And fs -> List.fold_left makeAnd presFormTrue fs
  | Alpha.Or fs -> List.fold_left makeOr presFormFalse fs
*)
  | Alpha.Less (it1, it2) -> Presburger.Less (intTermToAExp it1, intTermToAExp it2)
  | Alpha.Leq (it1, it2) -> Presburger.Leq (intTermToAExp it1, intTermToAExp it2)
  | Inteq (it1, it2) -> Eq (intTermToAExp it1, intTermToAExp it2)
  | Impl (f1, f2) -> Presburger.Or (Presburger.Not (bapaFormToPresForm f1), 
				    bapaFormToPresForm f2)
  | Bind (Forallint, i, f) -> Forall (i, bapaFormToPresForm f)
  | Bind (Existsint, i, f) -> Exists (i, bapaFormToPresForm f)
  | Bind (Forallnat, i, f) -> 
      let bf = bapaFormToPresForm f in
      let c = Less (Var i, Const 0) in
        Forall (i, Or (c, bf))
  | Bind (Existsnat, i, f) -> 
      let bf = bapaFormToPresForm f in
      let c = Leq (Const 0, Var i) in
        Exists (i, And (c, bf))
  | Bind (Forallset,i,f) 
  | Bind (Existsset,i,f) when not (occurs i f) -> 
      bapaFormToPresForm f
  | Bind(ForallProp,i,f)
  | Bind(ExistsProp,i,f) -> failwith "Bapapres: prop quantifier not handled yet"
  | _ -> failwith ("Bapapres.bapaFormToPresForm:
                 BAPA formula still contains non-Presburger construct\n" ^
		     Alpha.string_of_form bapa)

and makeAnd pf bf =
  let pfbf = bapaFormToPresForm bf in
    if pf = presFormTrue then
      pfbf
    else if pfbf = presFormTrue then
      pf
    else
      And (pf, pfbf)

and makeOr pf bf =
  let pfbf = bapaFormToPresForm bf in
    if pf = presFormFalse then
      pfbf
    else if pfbf = presFormFalse then
      pf
    else
      Or (pf, pfbf)



(*--------------------------------------------------
Testing
  --------------------------------------------------*)
(*
let _ = print_string "------------------------------\n"
let _ = print_string "------------------------------\n"

let pexample1 = bapaFormToPresForm (alpha example1)
let _ = print_string ((string_of_bool (omegaIsValid pexample1)) ^ "\n")

let pexample2 = bapaFormToPresForm (alpha example2)
let _ = print_string ((string_of_bool (omegaIsValid pexample2)) ^ "\n")

let pexample3 = bapaFormToPresForm (alpha example3)
let _ = print_string ((string_of_bool (omegaIsValid pexample3)) ^ "\n")

let pexample4 = bapaFormToPresForm (alpha example4)
let _ = print_string ((string_of_bool (omegaIsValid pexample4)) ^ "\n")

let pexample5 = bapaFormToPresForm (alpha example5)
let _ = print_string ((string_of_bool (omegaIsValid pexample5)) ^ "\n")

let pexample6 = bapaFormToPresForm (alpha example6)
let _ = print_string ((string_of_bool (omegaIsValid pexample6)) ^ "\n")

let pexample7 = bapaFormToPresForm (alpha example7)
let _ = print_string ((string_of_bool (omegaIsValid pexample7)) ^ "\n")

let pexample8 = bapaFormToPresForm (alpha example8)
let _ = print_string ((string_of_bool (omegaIsValid pexample8)) ^ "\n")

*)
