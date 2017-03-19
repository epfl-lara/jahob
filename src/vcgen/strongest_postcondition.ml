(** strongest postcondition path *)

open Ast
open Form
open FormUtil


(* {6 Debugging shorthands} *)

let debug_id : int = Debug.register_debug_module "Strongest_postcondition"
let debug_msg : (string -> unit) = Debug.debug_msg debug_id
let debug_lmsg = Debug.debug_lmsg debug_id
let debug_is_on ?(level=1) =
  fun () -> Debug.debug_is_on debug_id & !Debug.debug_level >= level


(*************************************************************************)
(* {6 Post-condition computation for each kind of basic commands without
      existential quantifiers for intermediate values}                   *)
(*************************************************************************)


let sp_Skip f = f

let sp_Hint _ f = f

(* Compute the strongest postcondition of f over (VarAssign ac),
   together with the new name for the old variable *)
let sp_VarAssign_aux ac f =
  let x = ac.assign_lhs in
  let x0 = Util.fresh_name x in
  let renameMap = [(x, mk_var x0)] in (* give a new name to the old value
                                         of the variable *)
  let f0 = subst renameMap f in (* substitute the new variable name in f *)
  let e0 = subst renameMap ac.assign_rhs in (* idem in e *)
  let f1 = smk_and [mk_eq (mk_var x, e0); f0] in
    (* Implicitly existential quantified on x0, must be on LHS of implication *)
    (x0, snd ac.assign_tlhs), smk_fixand_eq [x0] f1
      (* get rid of some equalities *)

let sp_VarAssign ac f = snd (sp_VarAssign_aux ac f)

let sp_Alloc ac f =
  let v = mk_var ac.alloc_lhs in
    smk_and [
      f;
      mk_elem (v, all_alloc_objsf);                (* x is allocated       *)
      mk_elem (v, mk_var (obj_var ac.alloc_type)); (* x has the right type *)
      mk_neq (v, mk_null)]                         (* x ~= null            *)

let sp_ArrayAlloc aac f =
  let x = aac.arr_alloc_lhs in
  let t = aac.arr_alloc_type in
    match aac.arr_alloc_dims with
      | [] -> Util.warn ("LoopInvariantInference: array " ^ x
                         ^ " has no dimension.\n"); f
      | [d] ->
	  let v = mk_var x in
	    smk_and [
              f;
              mk_elem (v, all_alloc_objsf);    (* x is allocated       *)
              mk_elem (v, mk_var (obj_var t)); (* x has the right type *)
              mk_neq (v, mk_null);             (* x ~= null            *)
              mk_eq (mk_arrayLength v, d)]     (* x..Array_length = d  *)
      | _ -> Util.warn ("LoopInvariantInference: array " ^ x 
                        ^ " has dimension greater than 2, not supported.\n"); f

let sp_Assert {hannot_form = af; hannot_msg = am} f = 
  smk_and [f; mk_comment am af]

let sp_NoteThat {hannot_form = af; hannot_msg = am} f =
  smk_and [f; mk_comment am af]

let sp_Assume {annot_form = af; annot_msg = am} f = 
  smk_and [f; mk_comment am af]

let sp_Split {annot_form = af; annot_msg = am} f =
  mk_comment am af

(* Compute the strongest postcondition of f over (Havoc hc),
   together with the new name of the old variables *)
let sp_Havoc_aux hc f =
  let havoc_var acc = function
    | Var x -> x :: acc
    | other -> Util.warn ("LoopInvariantInference: don't know how to havoc " ^ 
			    (PrintForm.string_of_form other) ^ "\n"); acc
  in
  let old_xs = List.fold_left havoc_var [] hc.havoc_regions in (* collect identifiers *)
  let new_xs = List.map Util.fresh_name old_xs in (* get fresh names *)
  let new_vs = List.map mk_var new_xs in (* make new variables *)
  let renameMap = List.combine old_xs new_vs in
  let f0 = subst renameMap f in (* substitute the new variable names in f *)
    match hc.havoc_constraint with
      | None -> new_xs, f0 (* no constraint on the variables *)
      | Some constr -> let constr0 = subst renameMap constr in
          (* substitute new variable names in the constraints *)
          new_xs, smk_and [constr0; f0]

let sp_Havoc hc f =
  if List.length hc.havoc_regions = 0 then f (* nothing to do here *)
  else
    let new_xs,f0 = sp_Havoc_aux hc f in
    let til = List.map (fun x -> (x, TypeUniverse)) new_xs in
      smk_exists (til, f0)

let sp_ProcCall (pc : proc_call) (f : form) : form =
  Util.fail "StrongestPostcondition: ProcCall should be desugared.\n"

let sp_bc bc f =
  match bc with
    | Skip -> sp_Skip f
    | Hint h -> sp_Hint h f
    | VarAssign ac -> sp_VarAssign ac f
    | Alloc ac -> sp_Alloc ac f
    | ArrayAlloc aac -> sp_ArrayAlloc aac f
    | Assert h -> sp_Assert h f
    | NoteThat nt -> sp_NoteThat nt f
    | Assume a -> sp_Assume a f
    | Split s -> sp_Split s f
    | Havoc hc -> sp_Havoc hc f
    | ProcCall pc -> sp_ProcCall pc f
    | Instantiate _ -> 
	Util.fail "sp_bc_asserts: instantiate should be desugared.\n"
    | Mp _ ->
	Util.fail "sp_bc_asserts: mp should be desugared.\n"


exception Invariant_violation

(* Strongest post-condition with loops unrolled i times. Returns true
   if successful, false if a loop invariant is violated. *)
let sp_unrolled f c i =

  (** Strongest post-condition for the command c under pre-condition f *)
  let rec sp_unrolled_rec (f : form) (c : command) : form =
    match c with
      | Basic {bcell_cmd = bc} -> sp_bc bc f
      | Seq cl -> List.fold_left sp_unrolled_rec f cl
      | Choice cl -> smk_or (List.map (sp_unrolled_rec f) cl)
      | If {if_condition = ic; if_then = it; if_else = ie} ->
          smk_or [
            sp_unrolled_rec (smk_and [f; ic]) it; (* true branch *)
            sp_unrolled_rec (smk_and [f; smk_not ic]) ie] (* false branch *)
      | Loop lc -> 
	  begin
	    match lc.loop_inv with
	      | None -> se_loop_unroll lc f i
	      | Some loop_inv -> se_loop_inv lc f loop_inv
	  end
      | Return {return_exp = re} ->
          begin 
	    match re with
	      | None -> f
	      | Some f0 -> smk_and [f; mk_eq (result_f, f0)]
          end
      | PickAny _ -> Util.fail "sp_unrolled: pickAny should be desugared.\n"
      | PickWitness _ -> Util.fail "sp_unrolled: pickWitness should be desugared.\n"
      | Assuming _ -> Util.fail "sp_unrolled: assuming should be desugared.\n"
      | Induct _ -> Util.fail "sp_unrolled: induct should be desugared.\n"
      | Contradict _ -> Util.fail "sp_unrolled: contradict should be desugared.\n"
      | Proof _ -> Util.fail "sp_unrolled: proof should be desugared.\n"

  (** Unrolls the non invariant loop i times and checks for exit after it *)
  and se_loop_unroll (lc : loop_command) (f : form) (j : int) : form =
    let after_prebody = sp_unrolled_rec f lc.loop_prebody in
      if j = 0 then (* exit from the loop *)
	smk_and [after_prebody; (smk_not lc.loop_test)]
      else
	let after_test = smk_and [after_prebody; lc.loop_test] in
	let after_postbody = sp_unrolled_rec after_test lc.loop_postbody in
	  (se_loop_unroll lc after_postbody (j - 1))

  (** Checks if the loop invariant can be violated during the loop *)
  and se_loop_inv (lc : loop_command) (f : form) (loop_inv : form) : form =
    let implies_inv = smk_impl (f, loop_inv) in
      if (not (Decider.valid implies_inv))
      then
        begin
	  debug_lmsg 1 (fun () -> "[not initially true]: "
		          ^ (PrintAst.pf implies_inv) ^ "\n");
	   raise Invariant_violation
        end
      else
	debug_lmsg 1 (fun () -> "[initially true]: "
		        ^ (PrintAst.pf implies_inv) ^ "\n");
      let after_prebody = sp_unrolled_rec loop_inv lc.loop_prebody in
      let after_test = smk_and [after_prebody; lc.loop_test] in
      let after_postbody = sp_unrolled_rec after_test lc.loop_postbody in
      let inductive = smk_impl (after_postbody, loop_inv) in
	if (not (Decider.valid inductive))
        then
          begin
	    debug_lmsg 1 (fun () -> "[not inductive]: "
			    ^ (PrintAst.pf inductive) ^ "\n");
	    raise Invariant_violation
          end
	else
          begin
	    debug_lmsg 1 (fun () -> "[inductive]: "
                            ^ (PrintAst.pf inductive) ^ "\n");
	    smk_and [after_prebody; (smk_not lc.loop_test)]
          end
  in
    try ignore (sp_unrolled_rec f c); true
    with Invariant_violation -> false


(*************************************************************************)
(*  {6 Full post-condition computation for each kind of basic commands}  *)
(*************************************************************************)


(* It roughly consists in putting assertions stating the existence of
   values satisfying the previous constrains

   Returns a couple whose first component is the resulting postcondition
   and the second is a list whose elements are assert statement formulae.
   We want to catch asserts failure even in choice statements where some
   branches might never be used: the second component is the assert
   statements that must always be true *)

let sp_Skip_asserts f_al = f_al

let sp_Hint_asserts h f_al = f_al

let sp_VarAssign_asserts ac (pre, asserts) =
  let typed_x0,f0 = sp_VarAssign_aux ac pre in
    smk_exists ([typed_x0], f0), asserts

let sp_Alloc_asserts ac (pre, asserts) =
  sp_Alloc ac pre, asserts

let sp_ArrayAlloc_asserts aac (pre, asserts) =
  sp_ArrayAlloc aac pre, asserts

let sp_Assert_asserts ({hannot_form = af} as assertion) (pre, asserts) =
  sp_Assert assertion pre, smk_impl (pre, af) :: asserts

let sp_NoteThat_asserts = sp_Assert_asserts
  
let sp_Assume_asserts a (pre, asserts) =
  sp_Assume a pre, asserts

let sp_Split_asserts ({annot_form = af} as split) (pre, asserts) =
  sp_Split split pre, smk_impl(pre, af) :: asserts

(* Compute the strongest postcondition of f over (Havoc hc).
   The only difference with sp_Havoc is that it tries to remove some
   equalities with smk_fixand_eq and it prints a debug message *)
let sp_Havoc_asserts hc (pre, asserts) =
  let new_xs, f0 = sp_Havoc_aux hc pre in
    debug_lmsg 1 ( fun () -> "Trying to remove: " 
                     ^ String.concat " " new_xs ^ "\n");
  let f1 = smk_fixand_eq new_xs f0 (* get rid of some equalities *) in
  let til = List.map (fun x -> (x, TypeUniverse)) new_xs in
    smk_exists (til, f1), asserts

let sp_ProcCall_asserts pc (pre, asserts) =
  sp_ProcCall pc pre, asserts

let sp_bc_asserts f_al bc =
  debug_lmsg 1 (fun () -> "sp_bc: fst arg1 = " ^ (PrintAst.pf (fst f_al))
                  ^ "\nsp_bc: arg2 = " ^ PrintAst.pr_basic_cmd bc ^ "\n");
  match bc with
    | Skip -> sp_Skip_asserts f_al
    | Hint h -> sp_Hint_asserts h f_al
    | VarAssign ac -> sp_VarAssign_asserts ac f_al
    | Alloc ac -> sp_Alloc_asserts ac f_al
    | ArrayAlloc aac -> sp_ArrayAlloc_asserts aac f_al
    | Assert h -> sp_Assert_asserts h f_al
    | NoteThat nt -> sp_NoteThat_asserts nt f_al
    | Assume a -> sp_Assume_asserts a f_al
    | Split s -> sp_Split_asserts s f_al
    | Havoc hc -> sp_Havoc_asserts hc f_al
    | ProcCall pc -> sp_ProcCall_asserts pc f_al
    | Instantiate _ -> 
	Util.fail "sp_bc_asserts: instantiate should be desugared.\n"
    | Mp _ ->
	Util.fail "sp_bc_asserts: mp should be desugared.\n"

  
(****************************************************)
(*  Full strongest post-condition path computation  *)
(****************************************************)

let rec sp_noloops ((f, asserts) as f_al) c =
  debug_lmsg 1 (fun () -> "Entering sp_noloops...\n");
  debug_lmsg 2 (fun () -> "analysing " ^ PrintAst.pr_command c ^ "\n");
  match c with
    | Basic {bcell_cmd = bc} -> sp_bc_asserts f_al bc
    | Seq cl -> List.fold_left sp_noloops f_al cl
        (* with Seq, the environment is modified by the successive commands.*)
    | Choice cl ->
        let f_l, a_l = List.split (List.map (sp_noloops f_al) cl) in
          smk_or f_l, List.concat a_l
    | If {if_condition = ic; if_then = it; if_else = ie} ->
        let true_f, true_al = sp_noloops (smk_and [f; ic], asserts) it in
        let false_f, false_al = sp_noloops (smk_and [f; smk_not ic], asserts) ie
        in
          smk_or [true_f; false_f], true_al @ false_al
    | Loop lc -> 
        Util.warn ("sp_noloops cannot handle:\n" ^ (PrintAst.pr_command c));
        mk_false, asserts
    | Return {return_exp = None} -> f_al
    | Return {return_exp = Some f0} ->
        smk_and [f; mk_eq (result_f, f0)], asserts
    | PickAny _ -> Util.fail ("sp_noloops: 'pickAny' should be desugared.\n")
    | PickWitness _ -> Util.fail ("sp_noloops: 'pickWitness' should be desugared.\n")
    | Assuming _ -> Util.fail ("sp_noloops: 'assuming' should be desugared.\n")
    | Induct _ -> Util.fail ("sp_noloops: 'induct' should be desugared.\n")
    | Contradict _ -> Util.fail ("sp_noloops: 'contradict' should be desugared.\n")    
    | Proof _ -> Util.fail ("sp_noloops: 'proof' should be desugared.\n")
