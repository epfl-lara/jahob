open Printf
open FolTranslation

let rec get_v_term : term -> ident list = function
  | _, `Int _ -> []
  | _, `Constant e -> [e]
  | _, `Variable _ -> []
  | _, `Function (f, args) -> f :: (List.concat (ListLabels.map ~f:get_v_term args))

let rec get_variables : fol_formula -> string list = function
  | #boool -> []

  | `Exists (_,f)
  | `Forall (_,f)
  | `Negation f -> get_variables f

  | `Equality (x,y) -> (get_v_term x) @ (get_v_term y)
  | `Predicate (_,args) -> List.concat (ListLabels.map ~f:get_v_term args)

  | `Disjunction fs
  | `Conjunction fs -> List.concat (ListLabels.map ~f:get_variables fs)
  
(* lots of room for optimisation *)

let rec count_relevant rel_set = function
  | [] -> 0
  | x::tail when List.mem x rel_set -> 1+(count_relevant rel_set tail)
  | _::tail -> count_relevant rel_set tail


let rec iterate (k:int) (threshold:float) (fs : (fol_formula * 'a * string list * float) array) vs = 
  let vs = ref vs in
  let n = Array.length fs - 1 in

    for i = 0 to n  do
      let (f, bidule, f_vars, f_score) = fs.(i) in
      let s = count_relevant !vs f_vars in
      let f_relevance = float_of_int s /. (float_of_int (List.length f_vars)) in
	fs.(i) <- (f, bidule, f_vars, f_score+.f_relevance);
	if f_score < threshold && f_score +. f_relevance >= threshold then
	  vs := f_vars @ !vs
    done;
    if k > 0 then iterate (k-1) threshold fs !vs
      


let sort_assumptions (goal:fol_formula) (hyps:('a * fol_formula) list) : ('a * fol_formula) list = 
  let fs = Array.of_list (List.map (fun (old_f, f) -> (f, old_f, get_variables f, 0.0) ) hyps) in
  let base_vs = get_variables goal in
    

    iterate 3 0.33 fs base_vs;
    let cmp = (fun (_,_,_,s1) (_,_,_,s2) -> compare s1 s2) in
      Array.stable_sort cmp fs;
      List.map (fun (f,old_f,_,_) -> (old_f, f)) (Array.to_list fs)



