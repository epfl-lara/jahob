open Util
open Form
open FormUtil
open Slice

let rec split_conjuncts f =
  match f with 
  | App (Const And, fs) ->
      List.concat (List.rev_map split_conjuncts fs)
  | App (Const Impl, (g::fs)) ->
      List.rev_map (curry smk_impl g)
      (List.concat (List.rev_map split_conjuncts fs)) 
  | _ -> [f]

let phase s fn x =
  Util.msg (s ^ "..."); 
  (if not !Util.verbose then Util.amsg(" (b)"));
  let res = fn x in
  Util.msg "done.\n";
  res

(** rewrite rtrancl over updated fields using the following equivalence
 *  (x,y) : {(x1,x2). (fieldWrite f s t) x1 = x2}^* 
 *  ==
 *  (x,y) : {(x1,x2). f x1 = x2 & x1 ~= s}^* |
 *  (x,s) : {(x1,x2). f x1 = x2}^* & (t,y) : {(x1,x2). f x1 = x2 & x1 ~= s}^*
 *)
let rewrite_upd_rtrancl f =
  let rec find_update x y fs acc =
    match fs with
    | App (Const Eq, [TypedForm (App (App (Const FieldWrite, [fld; s; t]), [px]), _); py])::fs'
    | App (Const Eq, [TypedForm (App (TypedForm (App (Const FieldWrite, [fld; s; t]), _), [px]), _); py])::fs'
    | App (Const Eq, [App (TypedForm (App (Const FieldWrite, [fld; s; t]), _), [px]); py])::fs'
    | App (Const Eq, [py; TypedForm (App (TypedForm (App (Const FieldWrite, [fld; s; t]), _), [px]), _)])::fs'
      when equal px x && equal py y ->
	let f_fld = mk_eq (App (fld, [x]), y) in
	let s_neq_x = mk_neq (s, x) in
	Some (s, t, smk_and (f_fld :: s_neq_x :: List.rev_append fs' acc), smk_and (f_fld :: List.rev_append fs' acc), fld)
    | App (Const And, more_fs)::fs' -> 
	find_update x y (List.rev_append more_fs fs') acc
    | f :: fs' -> find_update x y fs' (f :: acc)
    | [] -> None
  in
  let contains = function 
    | App (Const And, fs) -> 
	(fun f -> List.exists (equal f) fs)
    | _ -> (fun _ -> false)
  in
  let remove = function 
    | App (Const And, fs) ->
	(fun f -> smk_and (List.filter (fun f' -> not (equal f f')) fs))
    | f -> (fun _ -> f)
  in
  let rec r = function 
    | App (TypedForm (Var v, _), [Binder (Lambda, ([(x1, _); (x2, _)] as vs), f); x; y])
    | App (Var v, [Binder (Lambda, ([(x1, _); (x2, _)] as vs), f); x; y]) when v = str_rtrancl -> 
	( match find_update (mk_var x1) (mk_var x2) [f] [] with 
	| Some (s, t, restricted_f, new_f, fld) ->
	    let rtcl x y = App (Var str_rtrancl, [Binder (Lambda, vs, new_f); x; y]) in
	    let restricted_rtcl x y =
	      (* (x,y) : {(x1,x2). x2 = f x1 & x1 ~= x}^*   ==   x = y *)
	      (* (null, y) : {(x1,x2). x2 = f x1 & x1 ~= s}^*   ==   y = null *)
	      if equal x mk_null || contains restricted_f (mk_neq (x, mk_var x1)) then mk_eq (x, y) else 
	      (* (x,x) : {(x1, x2). F}^*  ==  True *)
	      if equal x y then mk_true else 
	      let restricted_f =
		(* (x,y) : {(x1, x2). F & x1 ~= y}^*  ==  (x,y) : {(x1,x2). F}^* *)
		if contains restricted_f (mk_neq (y, mk_var x1)) then
		  remove restricted_f (mk_neq (y, mk_var x1))
		else restricted_f 
	      in
	      App (Var str_rtrancl, [Binder (Lambda, vs, restricted_f); x; y]) 
	    in
	    let new_rtcl = mk_or [restricted_rtcl x y; mk_and [rtcl x s; restricted_rtcl t y]] in
	    r new_rtcl
	| None -> App (Var v, [Binder (Lambda, vs, r f); x; y]) )
    | App (fn, args) -> 
	App (r fn, List.map r args)
    | TypedForm (f, ty) -> TypedForm (r f, ty)
    | Binder (b, vs, f) -> Binder (b, vs, r f)
    | f -> f
  in r f
  

let normalize_form keep f0 = 
  (* let f1 = rewrite_upd_rtrancl f0 in *)
  let sq = sequent_of_form f0 in
  (* let (asms, conc) = slice [slice_obj_sets] env sq in *)
  let asms, conc = elim_fv_in_seq keep sq in
  unlambda (smk_impl (smk_and asms, conc)) 

let free_object_vars f =
  let filter env = 
    Util.filter_map (fun (_, ty) -> ty = mk_object_type) fst env
  in
  filter (get_annotated_types (normalize_form false f))

let is_oldform fv f =
  let rec check f = 
    match f with
    | App (Const Old, _)
    | Const And | Const Or | Const Not | Const Impl
    | Const Elem | Const Eq | Const Seteq | Const Subseteq | Const FieldRead -> true
    | Var v -> is_oldname v || List.mem v fv
    | TypedForm (f, _) -> check f
    | App (fn, ts) -> List.for_all check (fn :: ts)
    | _ -> false
  in check f

open Bf
open CachedDecider

module BfL = (Bf : Lattice with type t = Bf.t)

module BfCachedDecider = Make(BfL)


let background_marker = "__background"

let is_background = function
      |	App (Const Comment, [Const (StringConst b); _]) when b = background_marker -> true
      |	_ -> false

let _ = 
  let slice_mona_default env (asms, conc) =
    let asms' = List.filter (fun f -> disjoint ["Object"; "Array"] (fv f)) asms in
    (asms', conc)
  in
  let slice_cvcl_default _ (asms, conc) =
    (List.filter (fun f -> not (is_background f)) asms, conc)
  in
  BfCachedDecider.register_filter "mona" slice_mona_default;
  BfCachedDecider.register_filter "cvcl" slice_cvcl_default

let trivial_context = (Bf.top, fun _ -> mk_true)

let measure total_calls cached_calls acc_time f arg =
  let cached = (BfCachedDecider.stats ()).cache_hits in
  let time = (BfCachedDecider.stats ()).total_time in
  let res = f arg in
  let cached' = (BfCachedDecider.stats ()).cache_hits in
  let time' = (BfCachedDecider.stats ()).total_time in
  cached_calls := !cached_calls + (cached' - cached);
  total_calls := !total_calls + 1;
  acc_time := !acc_time +. (time' -. time);
  res
    
let measured_decide total_calls cached_calls acc_time context f =
  measure total_calls cached_calls acc_time (BfCachedDecider.decide context) f 

let measured_decide_fast total_calls cached_calls acc_time context f =
  measure total_calls cached_calls acc_time (BfCachedDecider.decide_fast context) f 

let entails_synt f g =
  let f_impl_g = smk_impl (f, g) in
  Util.safe_unsome false (Decider.test_valid (sequent_of_form f_impl_g))

module type PrioQueueElem =
  sig
    type el
    type context 

    val equal : el -> el -> bool
    val compare : context -> el -> el -> int
  end

module type PrioQueue =
  sig
    type el
    type context 
    type queue      
    val empty : queue
    val insert : context -> queue -> el -> queue
    val insert_top : context -> queue -> el -> queue
    val extract : context -> queue -> el * queue
    val remove_top : context -> queue -> queue
    val remove : context -> (el -> bool) -> queue -> queue
    val top : context -> queue -> el
    val length : queue -> int
  end
    
module PriorityQueue(Elem : PrioQueueElem) : (PrioQueue with type el = Elem.el and type context = Elem.context) =
   struct
     type el = Elem.el
     type context = Elem.context
     type queue = Empty | Node of el * queue * queue
     let empty = Empty
     
     let raise_empty () = raise (Failure "Priority queue: tried to extract from an empty queue")
	 
     let insert c queue elt =
       let rec insert queue elt =
       match queue with
       | Empty -> Node(elt, Empty, Empty)
       | Node(e, left, right) ->
           let comp_res = Elem.compare c elt e in
	   if comp_res < 0  then
	     Node(elt, insert right e, left)
           else if comp_res > 0 || not (Elem.equal e elt) then 
	     Node(e, insert right elt, left)
	   else queue
       in insert queue elt

     let insert_top c queue elt =
       let rec insert_top queue elt =
	 match queue with 
	 | Empty ->  Node(elt, Empty, Empty)
	 | Node(e, left, right) ->
             let comp_res = Elem.compare c elt e in
	     if comp_res > 0 then 
	       Node(e, insert_top right elt, left)
	     else if not (Elem.equal e elt) then
	       Node(elt, insert_top right e, left)
	     else queue
       in insert_top queue elt
	     

     let remove_top c = 
       let rec remove_top = function
	 | Empty -> raise_empty ()
	 | Node(elt, left, Empty) -> left
	 | Node(elt, Empty, right) -> right
	 | Node(elt, (Node(lelt, _, _) as left),
                (Node(relt, _, _) as right)) ->
		  if Elem.compare c lelt relt < 0
		  then Node(lelt, remove_top left, right)
		  else Node(relt, left, remove_top right)
       in remove_top

     let remove c remove_it = 
       let rec remove = function
	 | Empty -> Empty
	 | Node (elt, left, right) ->
	     let left' = remove left in
	     let right' = remove right in
	     if remove_it elt then remove_top c (Node (elt, left', right'))
	     else Node (elt, left', right')
       in remove

     let extract c = function
       | Empty -> raise_empty ()
       | Node(elt, _, _) as queue -> (elt, remove_top c queue)

     let top c = function 
       | Empty -> raise_empty ()
       | Node(elt, _, _) -> elt

     let rec length = function
       | Empty -> 0
       | Node (_, left, right) -> length left + length right + 1
   end
