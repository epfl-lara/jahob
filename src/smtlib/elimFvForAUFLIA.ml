(* Formula simplification, that, when having a choice, prefers the AFULIA logic to simplify into. *)

open Form
open LargeFormUtils

(** [smk_foralls_for_AUFLIA typed_id_list f]
    simplifies an all-quantified formula. Removes unused variables.
    Returns the resulting formula in the first component.
    The second component is true iff real simplification has happened. *)
let smk_foralls_for_AUFLIA  (typed_id_list : typedIdent list) (f:form) =
  let fvs = fv_set f in
  let isfree x = SetOfVars.mem x fvs in
  (* Walks through the variable list, determining for each variable whether it can be removed. *)
  let rec walk_through_xts sofar_id_list remaining_id_list sofar_simplified =
    (match remaining_id_list with
	[] -> (match sofar_id_list with
	    [] -> (f,true)
          | _ -> ((FormUtil.mk_foralls((List.rev sofar_id_list),f)), sofar_simplified))
      | (id,tf)::xts' -> 
	(if isfree id then walk_through_xts ((id,tf)::sofar_id_list) xts' sofar_simplified
	 else walk_through_xts sofar_id_list xts' true))
  in walk_through_xts [] typed_id_list false

(** [simplify_form_for_AUFLIA f]
    simplifies HOL formulas with regard to AUFLIA logic, rewriting as many formulas
    into AUFLIA as possible. In particular, prefer simplification into quantifiers 
    over simplification into set notation. Do not lose precision. *)
let simplify_form_for_AUFLIA (f:form) : form =
  (* [smk_seteq_for_AUFLIA f1 f2]
     simplifies the expression f1=f2. In particular, 
     if one of f1 or f2 is the empty set, and the other is a union over sets,
     unions are removed. If one of f1 or f2 is the empty set, and the other is a comprehension, the comprehension is removed.
     In the first component of the result the simpler formula is returned. The second component is true iff real simplification has happened. *)
  let rec smk_seteq_for_AUFLIA (f1:form) (f2:form) : (form*bool) =
    if FormUtil.equal f1 f2 then (FormUtil.mk_true,true)
    else (match (f1,f2) with
	(g,Const EmptysetConst) | (Const EmptysetConst,g) -> 
	  (match g with
	      Const EmptysetConst| App(Const Cup,[]) -> (FormUtil.mk_true, true)
 	    | App(Const Cup,[gg]) -> let (new_form,_) = smk_seteq_for_AUFLIA gg (Const EmptysetConst) in (new_form,true)
	    | App(Const Cup,lst) -> 
	      let list_of_equalities = List.rev_map (fun s -> let (new_eq,_) = smk_seteq_for_AUFLIA s (Const EmptysetConst) in new_eq) lst
	      in ((FormUtil.smk_and (List.rev list_of_equalities)),true)
	    (* | Binder(Comprehension,tvl,f) -> smk_foralls_for_AUFLIA til (smk_not_for_AUFLIA f) *) (* this is good, but not here *)
	    | _ -> ((FormUtil.mk_seteq (f1,f2)), false))
      | _ -> ((FormUtil.mk_seteq (f1,f2)), false))
  in
  (* [smk_cap_for_AUFLIA fs] 
     simplifies the intersection of sets from fs, returning in the second component
     - true, if something has changed during simplification,
     - false, if nothing has changed during simplification. *)     
  let smk_cap_for_AUFLIA (fs: form list) : (form * bool) =
    let rec scan_for_emptyset (to_go: form list) (sofar: form list) (empty_sofar:bool) (type_sofar: typeForm option) : (form*bool) =
      (match to_go with
	  [] ->
	    if empty_sofar then
	      match type_sofar with
		  None -> ((Const EmptysetConst),true)
		| Some ty -> ((FormUtil.mk_typedform (Const EmptysetConst,ty)),true)
	    else ((App(Const Cap, sofar)),false)
	| (TypedForm(Const EmptysetConst,ty))::xs -> ((FormUtil.mk_typedform (Const EmptysetConst,ty)),true)
	| ((TypedForm(f,ty)) as tf)::fs -> 
	  if empty_sofar then ((FormUtil.mk_typedform(Const EmptysetConst,ty)),true)
	  else scan_for_emptyset fs (tf::sofar) false (Some ty)
	| (Const EmptysetConst)::fs -> 
	    (match type_sofar with
		None -> scan_for_emptyset fs ((Const EmptysetConst)::sofar) true None
	      | Some ty -> ((FormUtil.mk_typedform(Const EmptysetConst,ty)),true))
	| f::fs -> scan_for_emptyset fs (f::sofar) empty_sofar type_sofar)
    in scan_for_emptyset fs [] false None
  in
  (* [smk_cup_for_AUFLIA fs]
     simplifies the union of sets from fs, returning in the second component
     - true, if something has changed during simplification,
     - false, if nothing has changed during simplification. *)
  let smk_cup_for_AUFLIA (fs:form list): (form*bool) =
    let rec scan_removing_emptyset (to_go: form list) (gone: form list) (type_sofar:typeForm option) (any_changes:bool) : (form*bool) =
      match to_go with
	  [] ->
	    (match type_sofar with
		Some ty -> 
		  (match gone with
		      [] -> ((FormUtil.mk_typedform (Const EmptysetConst,ty)),true)
		    | [g] -> ((attach_type_if_not_attached g ty),true)
		    | _ -> 
		      if any_changes then ((App (Const Cup, (List.rev_map (fun g -> attach_type_if_not_attached g ty) gone))),true)
		      else (App(Const Cup, gone),false))
	      | None -> 
		(match gone with
		    [] -> ((Const EmptysetConst),any_changes)
		  | [g] -> (g,true)
		  | _ -> ((App(Const Cup, gone)),any_changes)))
	| g::gs -> 
	  (match g with
	      TypedForm(Const EmptysetConst, ty) -> scan_removing_emptyset gs gone (Some ty) true
	    | TypedForm((App((Const Cup),lst)), ty) -> scan_removing_emptyset (List.rev_append lst gs) gone (Some ty) true
	    | TypedForm(g0, ty) -> scan_removing_emptyset gs (g::gone) (Some ty) any_changes
	    | Const EmptysetConst -> scan_removing_emptyset gs gone type_sofar true
	    | App((Const Cup),lst) -> scan_removing_emptyset (List.rev_append lst gs) gone type_sofar true
	    | _ -> scan_removing_emptyset gs (g::gone) type_sofar false
	  )
    in scan_removing_emptyset fs [] None false
  in
  (* [smk_or_for_AUFLIA fs]
     simplifies a disjunction over the formulas fs, returning in the second component
     - true, if something has changed during simplification,
     - false, if nothing has changed during simplification. *)
  let smk_or_for_AUFLIA (fs:form list) : (form*bool) =
    let rec throw_out_trivial (to_go : form list) (gone: form list) (any_changes:bool) : (form*bool) =
      match to_go with
	  [] -> 
	    (match gone with
		[] -> (FormUtil.mk_false,true)
	      | [x] -> (x,true)
	      | _ -> ((FormUtil.mk_or gone),any_changes))
	| g::gs -> 
	  (match g with
	      TypedForm(Const (BoolConst true),_)
	    | Const (BoolConst true) -> (FormUtil.mk_true,true)
	    | TypedForm(Const (BoolConst false),_)
	    | Const (BoolConst false) -> throw_out_trivial gs gone true
	    | _ -> throw_out_trivial gs (g::gone) any_changes)
    in throw_out_trivial fs [] false
  in
  (* [smk_eq_for_bapa f1 f2]
     simplifies an equality between f1 and f2, returning in the second component
     - true, if something has changed during simplification,
     - false, if nothing has changed during simplification. *)
  let smk_eq_for_bapa (f1:form) (f2:form) : (form*bool) =
    if f1=f2 then (FormUtil.mk_true, true) else ((FormUtil.mk_eq (f1,f2)), false)
  in
  (* [smk_not_for_AUFLIA f]
     simplifies the negation of f, returning in the second component
     - true, if something has changed during simplification,
     - false, if nothing has changed during simplification. *)
  let rec smk_not_for_AUFLIA : form -> (form*bool) = function
      Const (BoolConst b) -> ((Const (BoolConst (not b))),true)
    | TypedForm(Const (BoolConst b),ty) -> (FormUtil.mk_typedform ((Const (BoolConst (not b))),ty),true)
    | App(Const Not,[g]) -> (g,true)
    | App(Const Comment,[c;g]) -> ((App(Const Comment,[c;(fst (smk_not_for_bapa g))])),true)
    | f -> ((FormUtil.mk_not f),false)
  in 
  (* [simpl_form_aux f]
     simplifies f, returning in the second component
     - true, if something has changed during simplification,
     - false, if nothing has changed during simplification. *)
  let rec simpl_form_aux (f:form) : (form*bool) =
    let (f_new,b_new)=
      (match f with 
  	  App(f0,flst) -> 
 	    let (g,b) = simpl_form_aux f0 in
	    let (glst_rev,bl) = 
	      (List.fold_left
	         (fun (sofar_lst,sofar_bl) old_f -> 
		   let (new_f,bl) = simpl_form_aux old_f in
		   ((new_f::sofar_lst), (sofar_bl||bl))) ([],false) flst) in
            let glst = List.rev glst_rev in
	    (match (g,glst) with 
                ((Const Seteq),[g1;g2]) -> 
		  let (new_f,new_b) = smk_seteq_for_AUFLIA g1 g2 in (new_f,(b||bl||new_b))
	      | ((Const Cap),fs) -> 
                  let (new_f,new_b) = smk_cap_for_AUFLIA fs in (new_f,(b||bl||new_b))
	      | ((Const Cup),fs) -> 
		  let (new_f,new_b) = smk_cup_for_AUFLIA fs in (new_f,(b||bl||new_b))
	      | ((Const Or),fs) ->
		  let (new_f,new_b) = smk_or_for_AUFLIA fs in (new_f,(b||bl||new_b))
	      | ((Const Eq),[f1;f2]) ->
		  let (new_f,new_b) = smk_eq_for_AUFLIA f1 f2 in (new_f,(b||bl||new_b))
	      | ((Const Not), [f]) ->
		  let (new_f,new_b) = smk_not_for_AUFLIA f in (new_f,(b||bl||new_b))
    	      | _ -> (App(g,glst),(b||bl)))
        | Binder(bdr,typed_id_lst,f) -> 
            let (g0,b0) = simpl_form_aux f in
            (match bdr with 
                Forall -> 
                  let (g1,b1) = smk_foralls_for_AUFLIA typed_id_lst g0
                  in (g1,(b0||b1))
              | _ -> (Binder(bdr,typed_id_lst,g0),b0)
            )
        | TypedForm(f0,tf) -> 
            let (f1,b) = simpl_form_aux f0 in
	    (match f1 with
		TypedForm(f2,ty) -> ((FormUtil.mk_typedform(f2,tf)),true)
	      | _ -> ((FormUtil.mk_typedform(f1,tf)),b))
        | Var _ | Const _ -> (f, false))
    in if b_new then simpl_form_aux f_new else (f_new,false)
  in fst (simpl_form_aux f)

(** [subst_simplifying_for_AUFLIA m f]
    returns f with applied substitutions from m. *)
let rec subst_simplifying_for_AUFLIA (m:substVarForm) : form->form =
  let rec substm (f:form) : form =
    if MapOfVars.is_empty m then f else
      match f with
	  App(Const And, fs) -> FormUtil.smk_and (List.map substm fs)
	| App(Const MetaImpl,[f1;f2]) -> FormUtil.smk_metaimpl ((substm f1),(substm f2))
	| App(f1,fs) -> simplify_form_for_AUFLIA (App(substm f1, List.map substm fs))
	| Binder(k,tvs,f1) ->
	  let m1 = MapOfVars.filter (fun id _ -> not (List.mem_assoc id tvs)) m
	  (* m1 is projection of substitution to variables that are not bound *)
	  in
	  if MapOfVars.is_empty m1 then f else
            let (tvs1,renaming)= LargeFormUtils.capture_avoid (LargeFormUtils.fv_set_of_subst m1) tvs in
            let f2 = if MapOfVars.is_empty renaming then f1 else LargeFormUtils.nsubst renaming f1 in
            (match k with
                Forall -> FormUtil.smk_foralls (tvs1,(subst_simplifying_for_AUFLIA m1 f2))
	      | _ -> Binder(k,tvs1,(subst_simplifying_for_AUFLIA m1 f2)))
	| Var v -> (try MapOfVars.find v m with Not_found -> f)
	| Const _ -> f
	| TypedForm(f1,t) -> FormUtil.mk_typedform((substm f1),t)
  in substm

(** [subst_formlist_simplifying_for_AUFLIA var replacement fs]
    substitutes var by replacement in all the formulas of the list fs. *)
let subst_formlist_simplifying_for_bapa (var:ident) (replacement:form) : (form list) -> (form list) =
  let rec substm: (form -> form) = function
        App(Const And, fs) -> FormUtil.smk_and (substm_list fs)
      | App(Const MetaImpl, [f1;f2]) -> FormUtil.smk_metaimpl ((substm f1), (substm f2))
      | App(f1,fs) -> simplify_form_for_AUFLIA (App(substm f1, substm_list fs))
      | (Binder(k,tvs,f1)) as f -> 
          if List.mem_assoc var tvs then f
	  else
	    let (tvs1,renaming) = capture_avoid (LargeFormUtils.fv_set replacement) tvs in
	    let f2 = if MapOfVars.is_empty renaming then f1 else LargeFormUtils.nsubst renaming f1 in
	    let substituted_f2 = substm f2 in
	    (match k with
		Forall -> fst (smk_foralls_for_AUFLIA tvs1 substituted_f2)
	      | _ -> Binder(k,tvs1,substituted_f2))
      | (Var x) as f-> if x=var then replacement else f
      | (Const _) as f -> f
      | TypedForm(f1,t) -> FormUtil.mk_typedform((substm f1),t)
  and substm_list (fs: form list) : (form list) = List.map substm fs
  in substm_list

(** [elim_fv_in_seq_for_AUFLIA_opt k env s]
    where s is a sequent and env describes the types of its free variables,
    eliminates as many free variables from s as possible, using equalities in the assumptions, such that the resulting sequent is valid if and only if the original sequent is valid. If keep_pseudo is true, keeps the pseudo constants except in trivial cases. Also some simplifications happen.
    If no eliminations and no simplifications were possible, returns None.
    If some elimination or simplification has happened, returns Some (environment_describing_types_of_free_variables,sequent_after_eliminations).
*)
let elim_fv_in_seq_for_AUFLIA_opt (keep_pseudo:bool) (env:mapVarType) ((asms,conc):sequent) : ((mapVarType*sequent) option) =
  let rec substitute_and_elimfree (var_to_replace:ident) (replacement:form) (fs_todo: form list) (fs_done: form list) (changing_conc:form) (smaller_env:mapVarType) : ((mapVarType*sequent) option) =
    let sb = subst_formlist_simplifying_for_AUFLIA var_to_replace replacement in
    let new_fs_todo = sb fs_todo in
    let new_fs_done = sb fs_done in
    let new_smaller_env = MapOfVars.remove var_to_replace smaller_env in
    let new_changing_conc = subst_form_simplifying_for_AUFLIA var_to_replace replacement changing_conc in
    elimfree new_fs_todo new_fs_done new_changing_conc new_smaller_env true true
  and elimfree (fs_todo: form list) (fs_done: form list) (changing_conc:form) (smaller_env:mapVarType) (totally_changed:bool) (possibly_simplified_current_round:bool) : ((mapVarType*sequent) option) =
    (match fs_todo with
        [] -> if possibly_simplified_current_round then elimfree fs_done [] changing_conc smaller_env true false
              else if totally_changed then Some (smaller_env,(fs_done, changing_conc)) 
              else None
      | curr_asm::remaining_asms ->
          let var_in_others v = ((isfree_var_in_formlist v remaining_asms) || (isfree_var_in_formlist v fs_done) || (isfree_var v changing_conc)) in
          (match FormUtil.normalize 2 curr_asm with
              App (Const Eq, [Const (BoolConst true); rhs])
            | App (Const Eq, [rhs; Const (BoolConst true)]) -> 
                elimfree (rhs::remaining_asms) fs_done changing_conc smaller_env true true
            | App (Const Eq, [Const (BoolConst false); rhs])
            | App (Const Eq, [rhs; Const (BoolConst false)]) ->
                elimfree ((FormUtil.smk_not rhs)::remaining_asms) fs_done changing_conc smaller_env true true
            | App (Const Eq, [Var v1; Var v2])
            | App (Const Iff, [Var v1; Var v2])
            | App (Const Seteq, [Var v1; Var v2]) when v1=v2 ->
                let new_smaller_env = 
		  if (var_in_others v1) || (keep_pseudo && (List.mem v1 FormUtil.pseudo_constants)) then smaller_env
		  else MapOfVars.remove v1 smaller_env 
		in elimfree remaining_asms fs_done changing_conc new_smaller_env true possibly_simplified_current_round
            | App (Const Seteq, [Var v1; Var v2]) (* Here, v1 and v2 are different. *) ->
                if var_in_others v1 then
		  if keep_pseudo && (List.mem v1 FormUtil.pseudo_constants) then 
		    if List.mem v2 FormUtil.pseudo_constants then 
		      (* Both variables are pseudo constants. This fact is important, and the caller cares. *)
		      elimfree remaining_asms (curr_asm::fs_done) changing_conc smaller_env totally_changed possibly_simplified_current_round
		    else
		      if var_in_others v2 then
			(* v1 is a pseudo constant occuring elsewhere, v2 is not a pseudo constant, v2 occurs elsewhere. Replace v2 by v1. *)
			substitute_and_elimfree v2 (Var v1) remaining_asms fs_done changing_conc smaller_env
		      else
		        (* v1 is a pseudo constant occuring elsewhere, v2 is not a pseudo constant, v2 occurs nowhere else. Remove the equality. *)
			elimfree remaining_asms fs_done changing_conc (MapOfVars.remove v2 smaller_env) true possibly_simplified_current_round
		  else 
		    if keep_pseudo && (List.mem v2 FormUtil.pseudo_constants) then 
		      (* v1 is not a pseudo constant, v1 occurs elsewhere, v2 is a pseudo constant. Replace v1 by v2. *)
		      substitute_and_elimfree v1 (Var v2) remaining_asms fs_done changing_conc smaller_env
		    else
		      if var_in_others v2 then
		        (* Neither v1 nor v2 are pseudo constants or the caller does not care about pseudo constants. Both variables occur elewhere. Replace any variable by another one, e.g., v1 by v2.*)
			  substitute_and_elimfree v1 (Var v2) remaining_asms fs_done changing_conc smaller_env
		      else
			(* Neither v1 nor v2 are pseudo constants or the caller does not care about pseudo constants. v1 occurs elsewhere, v2 occurs nowhere else. Remove the equality. *)
			elimfree remaining_asms fs_done changing_conc (MapOfVars.remove v2 smaller_env) true possibly_simplified_current_round
                else 
		  if keep_pseudo && (List.mem v1 FormUtil.pseudo_constants) then 
		    if List.mem v2 FormUtil.pseudo_constants then 
		      (* Both variables are pseudo constants. This fact is important, and the caller probably cares. *)
		      elimfree remaining_asms (curr_asm::fs_done) changing_conc smaller_env totally_changed possibly_simplified_current_round
		    else
		      if var_in_others v2 then
                        (* v1 is a pseudo constant not occuring elsewhere, v2 is not a pseudo constant, v2 occurs elsewhere. Replace v2 by v1. *)
			substitute_and_elimfree v2 (Var v1) remaining_asms fs_done changing_conc smaller_env
		      else
			(* v1 is a pseudo constant not occuring elsewhere, v2 is not a pseudo constant, v2 occurs nowhere else. Remove the equality. *)
			elimfree remaining_asms fs_done changing_conc (MapOfVars.remove v2 smaller_env) true possibly_simplified_current_round
		  else
		    let env_without_v1 = MapOfVars.remove v1 smaller_env in
		    if keep_pseudo && (List.mem v2 FormUtil.pseudo_constants) then 
		      (* v1 is not a pseudo constant, v1 does not occur elsewhere, v2 is a pseudo constant. Remove the equality. *)
		      elimfree remaining_asms fs_done changing_conc env_without_v1 true possibly_simplified_current_round
		    else
		      if var_in_others v2 then
                        (* Neither v1 nor v2 are pseudo constants or the caller does not care about pseudo constants. v1 does not occur elsewhere, v2 occurs elsewhere. Remove the equation.*)
			elimfree remaining_asms fs_done changing_conc env_without_v1 true possibly_simplified_current_round
		      else
			(* Neither v1 nor v2 are pseudo constants or the caller does not care about pseudo constants. Neither v1 nor v2 occur elsewhere. Remove the equality. *)
			elimfree remaining_asms fs_done changing_conc (MapOfVars.remove v2 env_without_v1) true possibly_simplified_current_round
            | App (Const Eq, [Var v; rhs])
            | App (Const Eq, [rhs; Var v])
            | App (Const Iff, [Var v; rhs])
            | App (Const Iff, [rhs; Var v])
            | App (Const Seteq, [rhs; Var v])
            | App (Const Seteq, [Var v; rhs]) ->
                if (isfree_var v rhs) || (keep_pseudo && (List.mem v FormUtil.pseudo_constants)) then 
		  elimfree remaining_asms (curr_asm::fs_done) changing_conc smaller_env totally_changed possibly_simplified_current_round
                else substitute_and_elimfree v rhs remaining_asms fs_done changing_conc smaller_env
	    | App(Const Subseteq, [f1;f2]) when FormUtil.equal f1 f2 -> 
	        let fv_of_f1_f2 = fv_set f1 in
                let new_env = 
		  SetOfVars.fold 
		    (fun next_fvr sofar -> if var_in_others next_fvr then sofar else SetOfVars.remove next_fvr sofar)
		    fv_of_f1_f2
		    smaller_env in
                elimfree remaining_asms fs_done changing_conc new_env true possibly_simplified_current_round
	    (* | App(Const Eq, [Const EmptysetConst; rhs])
	       | App(Const Eq, [rhs; Const EmptysetConst])
	       | App(Const Seteq, [Const EmptysetConst; rhs])
	       | App(Const Seteq, [rhs; Const EmptysetConst]) ->  TODO *)
            | Var v ->
	        if keep_pseudo && (List.mem v FormUtil.pseudo_constants) then
		  elimfree remaining_asms (curr_asm::fs_done) changing_conc smaller_env totally_changed possibly_simplified_current_round
		else
                  substitute_and_elimfree v FormUtil.mk_true remaining_asms fs_done changing_conc smaller_env
            | App(Const Not,[Var v]) ->
	        if keep_pseudo && (List.mem v FormUtil.pseudo_constants) then
		  elimfree remaining_asms (curr_asm::fs_done) changing_conc smaller_env totally_changed possibly_simplified_current_round
		else
                  substitute_and_elimfree v FormUtil.mk_false remaining_asms fs_done changing_conc smaller_env
            | _ -> elimfree remaining_asms (curr_asm::fs_done) changing_conc smaller_env totally_changed possibly_simplified_current_round
          )
    )
  in elimfree asms [] conc env false false

(** [elim_fv_in_seq_for_AUFLIA k s env]
    where s is a sequent and env describes the types of its free variables,
    eliminates as many free variables from s as possible, using equalities in the assumptions, such that the resulting sequent is valid if and only if the original sequent is valid. If keep_pseudo is true, keeps the pseudo constants except in trivial cases. Also some simplifications happen.
    Returns the pair (environment_describing_types_of_free_variables, sequent_after_eliminations).
*)
let elim_fv_in_seq_for_AUFLIA (keep_pseudo:bool) (env:mapVarType) (s:sequent) : ((mapVarType*sequent) option) =
  match elim_fv_in_seq_for_AUFLIA_opt keep_pseudo env s with
      None -> (env,s)
    | Some (env1,s1) -> (env1,s1)
