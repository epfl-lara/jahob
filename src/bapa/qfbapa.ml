(** Creating polynomially sized quantifier-free Presburger arithmetic formula
    given a quantifier-free BAPA formula. 
   
    Algorithm and implementation by Viktor Kuncak, see

@TechReport{Kuncak07QuantifierFreeBAPAinNP,
  author =       {Viktor Kuncak},
  title =        {Quantifier-Free Boolean Algebra with Presburger Arithmetic is NP-complete},
  institution =  {MIT CSAIL},
  year =         2007,
  month =        {January},
  number = {MIT-CSAIL-TR-2007-001},
  url = {\url{http://hdl.handle.net/1721.1/35258}}
}

@PhdThesis{Kuncak07DecisionProceduresModularDataStructureVerification,
  author =       {Viktor Kuncak},
  title =        {Modular Data Structure Verification},
  school =       {EECS Department, Massachusetts Institute of Technology},
  month = {February},
  year =         {2007},
}

*)

open Alpha
open Nlogn
open Bapaform

let rec from_to_list a b = if a > b then [] else a :: from_to_list (a+1) b
let prop_var (i_n : int) (set_id : ident) : ident =
  "pp_" ^ string_of_int i_n ^ "_" ^ set_id
let nat_var (i_n : int) : ident =
    "ll_" ^ string_of_int i_n

let mk_ifThenElse (f1 : form) (it1 : intTerm) (it2 : intTerm) =
  if f1=True then it1
  else if f1=False then it2
  else IfThenElse(f1,it1,it2)

(** used for pa_of_ba_term *)
let rec set_repl (k : int) (st : setTerm) : form =
  match st with
    | Setvar id -> PropVar (prop_var k id)
    | Emptyset -> False
    | Fullset -> True
    | Complement st1 -> Not (set_repl k st1)
    | Union sts -> Or (List.map (set_repl k) sts)
    | Inter sts -> And (List.map (set_repl k) sts)

(** Generate formula of the form
      (if st0 then l_k else 0)
    where st0 is the result of replacing, in st, the set variables with k-family
    of propositional variables, as given by set_repl.
*)
let pa_of_ba_term (st : setTerm) (k : int) : intTerm =
  mk_ifThenElse
    (set_repl k st)
    (Intvar (nat_var k))
    (Const 0)

(*
  let rec c_sum (acc : int) (accit : intTerm list) (its : intTerm list) : intTerm = 
  match its with
    | [] -> 
	(match accit with
	   | [] -> Const acc
	   | _ -> Plus (Const acc :: List.rev accit)
	)
    | Const k::its1 -> c_sum (k+acc) accit its1
    | Plus its0::its1 -> c_sum acc accit (its0 @ its1)
    | it::its1 -> c_sum acc (it::accit) its1
  let smk_Plus (sts : intTerm list) : intTerm =
    c_sum 0 [] sts
*)

(** translate BA to PA expression *)
let rec pa_of_ba (n : int) (st : setTerm) : intTerm =
  Plus (List.map (pa_of_ba_term st) (from_to_list 1 n))

(** reduce QFBAPA formula f to QFPA formula,
    introducing only n generic partition cardinality variables *)
let rec reduce (n : int) (f : form) : form =
  (* pre: f is in nnf *)
  match f with
    | PropVar _ | True | False -> f
    | Inteq(it1,it2) -> Inteq(int_reduce n it1,int_reduce n it2)
    | Less(it1,it2) -> Less(int_reduce n it1,int_reduce n it2)
    | Leq(it1,it2) -> Leq(int_reduce n it1,int_reduce n it2)
    | Not f1 -> Not (reduce n f1)
    | And fs -> And (List.map (reduce n) fs)
    | Or fs -> Or (List.map (reduce n) fs)
    | Impl(_,_) -> failwith "Qfbapa.reduce: unexpected Impl"
    | Bind(_,_,_) -> failwith "Qfbapa.reduce: unexpected binder"
    | Subseteq(_,_) -> failwith "Qfbapa.reduce: unexpected Subseteq"
    | Seteq(_,_) -> failwith "Qfbapa.reduce: unexpected Seteq"
and int_reduce (n : int) (it : intTerm) : intTerm = 
  match it with
    | Intvar _ | Const _ -> it
    | Plus its -> Plus (List.map (int_reduce n) its)
    | Minus(it1,it2) -> Minus(int_reduce n it1, int_reduce n it2)
    | Times(k,it1) -> Times(k,int_reduce n it1)
    | IfThenElse(f1,it1,it2) -> 
	mk_ifThenElse 
	  (reduce n f1)
	  (int_reduce n it1)
	  (int_reduce n it2)
    | Div(it1,k) -> Div(int_reduce n it1,k)
    | Card st -> pa_of_ba n st

let count_card_exprs_by_type (f : form) : int * int =
  (* assumes we are checking for validity *)
  let big = ref 0 in
  let small = ref 0 in
  let inc_big() = (big := !big + 1) in
  let inc_small() = (small := !small + 1) in
  let rec count_card_exprs (f : form) : unit =
    match f with
      | Not f1 -> atom_count_card_exprs false f1
      | And fs | Or fs -> ListLabels.iter ~f:count_card_exprs fs
      | Impl(_,_) -> failwith "Qfbapa.count_card: unexpected Impl"
      | Bind(_,_,_) -> failwith "Qfbapa.count_card: unexpected binder"
      | _ -> atom_count_card_exprs true f
  and atom_count_card_exprs (positive : bool) (f : form) : unit =
    match f with
      | PropVar _ | True | False -> ()
      | Inteq(Card st1,Const 0) 
      | Leq(Card st1,Const 0)
      | Less(Card st1, Const 1)
	-> if positive then inc_small() else ()
      | Inteq(Card st1,Const 1) 
      | Leq(Card st1,Const 1) 
      | Less(Card st1,Const 2)
	-> if positive then inc_big() else inc_small()
      | Inteq(it1,it2)
      | Less(it1,it2) 
      | Leq(it1,it2) -> (int_count_card_exprs it1; int_count_card_exprs it2)
      | Subseteq(_,_) -> ()
      | Seteq(_,_) -> ()
      | Not _ | And _ | Or _ | Impl(_,_) | Bind(_,_,_) -> 
	  failwith "Qfbapa.atom_count_card_exprs: not in negation normal form"
  and int_count_card_exprs (it : intTerm) : unit = 
    match it with
      | Intvar _ | Const _ -> ()
      | Plus its -> ListLabels.iter ~f:int_count_card_exprs its
      | Minus(it1,it2) -> (int_count_card_exprs it1; int_count_card_exprs it2)
      | Times(k,it1) -> int_count_card_exprs it1
      | IfThenElse(f1,it1,it2) -> 
	  (count_card_exprs f1;
	   int_count_card_exprs it1;
	   int_count_card_exprs it2)
      | Div(it1,k) -> int_count_card_exprs it1
      | Card st -> inc_big()
  in
    count_card_exprs f;
    (!big, !small)

(** state that cardinality variable is non-negative *)
let mk_card_non_neg (i : int) = Leq(Const 0, Intvar (nat_var i))
let cards_non_neg (n : int) = List.map mk_card_non_neg (from_to_list 1 n)

(** symmetry_breaking predicate says that 
    propositional variables denote a strictly increasing sequence of regions *)
let use_symmetry_breaking = ref true
let prop_less (s : ident) (i : int) : form = 
  And[Not (PropVar (prop_var i s));
      PropVar (prop_var (i+1) s)]
let prop_eq (s : ident) (i : int) : form =
  Or[And [Not (PropVar (prop_var i s));
	  Not (PropVar (prop_var (i+1) s))];
     And [PropVar (prop_var i s);
	  PropVar (prop_var (i+1) s)]]
let rec mk_index_less (sets : ident list) (i : int) : form = 
  match sets with
    | [] -> True
    | [s] -> prop_less s i
    | s::sets1 -> 
	Or [prop_less s i;
	    And [prop_eq s i; mk_index_less sets1 i]]
let symmetry_breaking (n : int) (sets : ident list) = 
  if !use_symmetry_breaking then
    if n <= 1 then [] else 
      List.map (mk_index_less sets) (from_to_list 1 (n - 1))
  else []

let compute_n (f : form) : int =
  let f1 = negation_normal_form (simplify_set_relations f) in
  let (d, b) = count_card_exprs_by_type f1 in
  let n0 = find_sparseness_bound d in
    n0 + b

(** top-level translation function for fixed or computed bound *)
let reduce_to_pa (given_n : int) (f : form) : form = 
  let sets = set_vars_of f in
  let f1 = negation_normal_form (simplify_set_relations f) in
  let (d, b) = count_card_exprs_by_type f1 in
  let n0 = find_sparseness_bound d in
  let n1 = n0 + b in
  let n = if given_n > 0 then given_n else n1 in
  let _ = Util.msg 
    (Printf.sprintf "QFBAPA: d=%d big dims, b=%d small dims, b+N(d)=%d,  S=%d sets" 
       d b n (List.length sets)) in
  let body = reduce n f1 
  in
    Impl(And (symmetry_breaking n sets @ cards_non_neg n), 
	 body)

let rec iter_check (n : int) (maxn : int) (check : form -> bool) (sets : ident list) (f : form) : bool option =
  let _ = Util.msg(Printf.sprintf "Iteration %d / %d\n" n maxn) in
    if check (Impl(And (symmetry_breaking n sets @ cards_non_neg n), 
		   reduce n f))
    then (if (n >= maxn) then Some true
	  else iter_check (n+1) maxn check sets f)
    else None

let rec power2 (x : int) : int =
  if x<=0 then 1
  else 2 * power2 (x - 1)

let bound_n (n : int) (s : int) : int =
  if s >= 15 then (if n < 16000 then n else Util.fail "This call to qfbapa is infeasible, the bound on n is too big")
  else
    let sexp = power2 s in
      if n >= sexp then 
	(Util.msg (Printf.sprintf ("Set bound 2^s (%d) is lower than d log d bound (%d), using 2^s for soundness, " ^^
		     "but you better use fullbapa option anyway.\n") sexp n);
	 sexp)
      else n

(** more general top-level translation function that also decides the truth value and can do iteration *)
let check_qfbapa (given_n : int) (iterative : bool) (check : form -> bool) (f : form) : bool option = 
  let sets = set_vars_of f in
  let f1 = negation_normal_form (simplify_set_relations f) in
  let (d, b) = count_card_exprs_by_type f1 in
  let n0 = find_sparseness_bound d in
  let n1 = n0 + b in
  let n_required = if given_n > 0 then given_n else n1 in
  let n = bound_n n_required (List.length sets) in
    iter_check (if iterative then 1 else n) n check sets f1
