(* The decision module tries to get rid of cardinalities of comprehensions over finite types in a sequent in way which is always sound for validity and 
   as complete as possible. The used method transforms the comprehesions into letters and tries to derive relations between them using standard
   decision procedures. *)

open Form
open LargeFormUtils

(** [smk_foralls_for_bapa (typed_id_list,f)]
    simplifies an all-quantified formula. Removes unused variables.
    Simplifies "for all x: x not in S" where x does not occur in S 
    into "S=emptyset". Returns the resulting formula in the first component.
    The second component is true iff real simplification has happened. *)
let smk_foralls_for_bapa (typed_id_list : typedIdent list) (f:form) =
  let fvs = fv_set f in
  let isfree x = SetOfVars.mem x fvs in
  (* Walks through the variable list, determining for each variable whether it can be removed. *)
  let rec walk_through_xts sofar_f sofar_id_list remaining_id_list sofar_simplified =
    (match remaining_id_list with
	[] -> (match sofar_id_list with
	    [] -> (sofar_f,true)
          | _ -> ((FormUtil.mk_foralls(sofar_id_list,sofar_f)), sofar_simplified))
      | (id,tf)::xts' -> (if isfree id then 
	  (match sofar_f with 
	      TypedForm(App(Const Not,[App(Const Elem,[TypedForm ((Var id1),tf1);(TypedForm(some_set,TypeApp(TypeSet,[tf2]))) as typed_set])]),TypeApp(TypeBool,[])) when (id=id1 && tf=tf1 && tf1=tf2 && not (isfree_var id some_set)) -> 
		walk_through_xts (TypedForm(App((Const Seteq),[typed_set;(TypedForm((Const EmptysetConst),(TypeApp(TypeSet,[tf]))))]),TypeApp(TypeBool,[]))) sofar_id_list xts' true
	    | _ -> walk_through_xts sofar_f ((id,tf)::sofar_id_list) xts' sofar_simplified)
	else walk_through_xts sofar_f sofar_id_list xts' true))
  in walk_through_xts f [] typed_id_list false

(** [simplify_form_for_bapa f]
    simplifies HOL formulas with regard to BAPA logic, rewriting as many formulas
    into BAPA as possible. In particular, prefer simplification into set notation
    over simplification into quantifiers. Do not lose precision. *)
let simplify_form_for_bapa (f:form) : form =
  (* [smk_seteq_for_bapa f1 f2]
     simplifies the expression f1=f2. In particular, 
     if one of f1 or f2 is the empty set, and the other is a union,
     more equalities are derived. In the first component of the result 
     the simpler formula is returned. The second component is true iff 
     real simplification has happened.
  *)
  let rec smk_seteq_for_bapa (f1:form) (f2:form) : (form*bool) =
    if FormUtil.equal f1 f2 then (FormUtil.mk_true,true)
    else (match (f1,f2) with
	(g,Const EmptysetConst) | (Const EmptysetConst,g) -> 
	  (match g with 
	      App(Const Cup,[]) -> (FormUtil.mk_true, true)
	    | App(Const Cup,[gg]) -> let (new_form,_) = smk_seteq_for_bapa gg (Const EmptysetConst) in (new_form,true)
	    | App(Const Cup,lst) -> 
	      let list_of_equalities = List.rev_map (fun s -> let (new_eq,_) = smk_seteq_for_bapa s (Const EmptysetConst) in new_eq) lst
	      in ((FormUtil.smk_and list_of_equalities),true)
	    | _ -> ((FormUtil.mk_seteq (f1,f2)), false))
      | _ -> ((FormUtil.mk_seteq (f1,f2)), false))
  in
  (* [smk_cap_for_bapa fs] 
     simplifies the intersection of sets from fs, returning in the second component
     - true, if something has changed during simplification,
     - false, if nothing has changed during simplification. *)     
  let smk_cap_for_bapa (fs: form list) : (form * bool) =
    let rec scan_for_emptyset (to_go: form list) (sofar: form list) (empty_sofar:bool) (type_sofar: typeForm option) : (form*bool) =
      (match to_go with
	  [] ->
	    if empty_sofar then
	      match type_sofar with
		  None -> ((Const EmptysetConst),true)
		| Some ty -> ((TypedForm(Const EmptysetConst,ty)),true)
	    else ((App(Const Cap, sofar)),false)
	| (TypedForm(Const EmptysetConst,ty))::xs -> ((TypedForm(Const EmptysetConst,ty)),true)
	| ((TypedForm(f,ty)) as tf)::fs -> 
	    if empty_sofar then ((TypedForm(Const EmptysetConst,ty)),true)
	    else scan_for_emptyset fs (tf::sofar) false (Some ty)
	| (Const EmptysetConst)::fs -> 
	    (match type_sofar with
		None -> scan_for_emptyset fs ((Const EmptysetConst)::sofar) true None
	      | Some ty -> ((TypedForm(Const EmptysetConst,ty)),true))
	| f::fs -> scan_for_emptyset fs (f::sofar) empty_sofar type_sofar)
    in scan_for_emptyset fs [] false None
  in
  (* [smk_cup_for_bapa fs]
     simplifies the union of sets from fs, returning in the second component
     - true, if something has changed during simplification,
     - false, if nothing has changed during simplification. *)
  let smk_cup_for_bapa (fs:form list): (form*bool) =
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
	      TypedForm(Const EmptysetConst, ty) -> 
		scan_removing_emptyset gs gone (Some ty) true
	    | TypedForm((App((Const Cup),lst)), ty) -> scan_removing_emptyset (List.rev_append lst gs) gone (Some ty) true
	    | TypedForm(g0, ty) -> scan_removing_emptyset gs (g::gone) (Some ty) any_changes
	    | Const EmptysetConst -> scan_removing_emptyset gs gone type_sofar true
	    | App((Const Cup),lst) -> scan_removing_emptyset (List.rev_append lst gs) gone type_sofar true
	    | _ -> scan_removing_emptyset gs (g::gone) type_sofar false
	  )
    in scan_removing_emptyset fs [] None false
  in
  (* [smk_or_for_bapa fs]
     simplifies a disjunction over the formulas fs, returning in the second component
     - true, if something has changed during simplification,
     - false, if nothing has changed during simplification. *)
  let smk_or_for_bapa (fs:form list) : (form*bool) =
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
  (* [smk_not_for_bapa f]
     simplifies the negation of f, returning in the second component
     - true, if something has changed during simplification,
     - false, if nothing has changed during simplification. *)
  let rec smk_not_for_bapa : form -> (form*bool) = function
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
		  let (new_f,new_b) = smk_seteq_for_bapa g1 g2 in (new_f,(b||bl||new_b))
	      | ((Const Cap),fs) -> 
                  let (new_f,new_b) = smk_cap_for_bapa fs in (new_f,(b||bl||new_b))
	      | ((Const Cup),fs) -> 
		  let (new_f,new_b) = smk_cup_for_bapa fs in (new_f,(b||bl||new_b))
	      | ((Const Or),fs) ->
		  let (new_f,new_b) = smk_or_for_bapa fs in (new_f,(b||bl||new_b))
	      | ((Const Eq),[f1;f2]) ->
		  let (new_f,new_b) = smk_eq_for_bapa f1 f2 in (new_f,(b||bl||new_b))
	      | ((Const Not), [f]) ->
		  let (new_f,new_b) = smk_not_for_bapa f in (new_f,(b||bl||new_b))
    	      | _ -> (App(g,glst),(b||bl)))
        | Binder(bdr,typed_id_lst,f) -> 
            let (g0,b0) = simpl_form_aux f in
            (match bdr with 
                Forall -> 
                  let (g1,b1) = smk_foralls_for_bapa typed_id_lst g0
                  in (g1,(b0||b1))
              | _ -> (Binder(bdr,typed_id_lst,g0),b0)
            )
        | TypedForm(f0,tf) -> 
            let (f1,b) = simpl_form_aux f0 in
	    (match f1 with
		TypedForm(f2,ty) -> ((TypedForm(f2,tf)),true)
	      | _ -> (TypedForm(f1,tf),b))
        | Var _ | Const _ -> (f, false))
    in if b_new then simpl_form_aux f_new else (f_new,false)
  in fst (simpl_form_aux f)

(** [subst m f]
    returns f with applied substitutions from m. *)
let rec subst (m:mapVarForm) : form->form =
  let rec substm (f:form) : form =
    if MapOfVars.is_empty m then f else
      match f with
	  App(Const And, fs) -> FormUtil.smk_and (List.map substm fs)
	| App(Const MetaImpl,[f1;f2]) -> FormUtil.smk_metaimpl ((substm f1),(substm f2))
	| App(f1,fs) -> simplify_form_for_bapa (App(substm f1, List.map substm fs))
	| Binder(k,tvs,f1) ->
	  let m1 = MapOfVars.filter (fun id _ -> not (List.mem_assoc id tvs)) m
	  (* m1 is projection of substitution to variables that are not bound *)
	  in
	  if MapOfVars.is_empty m1 then f else
            let (tvs1,renaming)= LargeFormUtils.capture_avoid (LargeFormUtils.fv_set_of_subst m1) tvs in
            let f2 = if MapOfVars.is_empty renaming then f1 else LargeFormUtils.nsubst renaming f1 in
            (match k with
                Forall -> FormUtil.smk_foralls (tvs1,(subst m1 f2))
	      | _ -> Binder(k,tvs1,(subst m1 f2)))
	| Var v -> (try MapOfVars.find v m with Not_found -> f)
	| Const _ -> f
	| TypedForm(f1,t) -> FormUtil.mk_typedform((substm f1),t)
  in substm

(** [subst_formlist_simplifying_for_bapa var replacement fs]
    substitutes var by replacement in all the formulas of the list fs. *)
let subst_formlist_simplifying_for_bapa (var:ident) (replacement:form) : (form list) -> (form list) =
  let rec substm: (form -> form) = function
        App(Const And, fs) -> FormUtil.smk_and (substm_list fs)
      | App(Const MetaImpl, [f1;f2]) -> FormUtil.smk_metaimpl ((substm f1), (substm f2))
      | App(f1,fs) -> simplify_form_for_bapa (App(substm f1, substm_list fs))
      | (Binder(k,tvs,f1)) as f -> 
          if List.mem_assoc var tvs then f
	  else
	    let (tvs1,renaming) = LargeFormUtils.capture_avoid (LargeFormUtils.fv_set replacement) tvs in
	    let f2 = if MapOfVars.is_empty renaming then f1 else LargeFormUtils.nsubst renaming f1 in
	    let substituted_f2 = substm f2 in
	    (match k with
		Forall -> fst (smk_foralls_for_bapa tvs1 substituted_f2)
	      | _ -> Binder(k,tvs1,substituted_f2))
      | (Var x) as f-> if x=var then replacement else f
      | (Const _) as f -> f
      | TypedForm(f1,t) -> FormUtil.mk_typedform((substm f1),t)
  and substm_list (fs: form list) : (form list) = List.map substm fs
  in substm_list

(** [subst_form_simplifying_for_bapa var replacement f]
    substitutes var by replacement in the formula f. *)
let subst_form_simplifying_for_bapa (var:ident) (replacement:form) : (form -> form) =
  let rec substm: (form -> form) = function
        App(Const And, fs) -> FormUtil.smk_and (substm_list fs)
      | App(Const MetaImpl, [f1;f2]) -> FormUtil.smk_metaimpl ((substm f1), (substm f2))
      | App(Const Cap, [TypedForm(Const EmptysetConst,ty);_])
      | App(Const Cap, [_;TypedForm(Const EmptysetConst,ty)]) -> TypedForm(Const EmptysetConst,ty)
      | App(f1,fs) -> simplify_form_for_bapa (App(substm f1, substm_list fs))
      | (Binder(k,tvs,f1)) as f -> 
          if List.mem_assoc var tvs then f
	  else
	    let (tvs1,renaming) = capture_avoid (fv_set replacement) tvs in
	    let f2 = if MapOfVars.is_empty renaming then f1 else nsubst renaming f1 in
	    let substituted_f2 = substm f2 in
	    (match k with
		Forall -> fst (smk_foralls_for_bapa tvs1 substituted_f2)
	      | _ -> Binder(k,tvs1,substituted_f2))
      | (Var x) as f-> if x=var then replacement else f
      | (Const _) as f -> f
      | TypedForm(f1,t) -> FormUtil.mk_typedform((substm f1),t)
  and substm_list (fs: form list) : (form list) = List.map substm fs
  in substm

(** [elim_fv_in_seq_for_bapa s env]
    where s is a sequent and env describes the types of its free variables,
    eliminates as many free variables from s as possible, using equalities in the assumptions, such that the resulting sequent is valid if and only if the original sequent is valid. Also some simplifications happen.
    If no eliminations and no simplifications were possible, returns None.
    If some elimination or simplification has happened, returns Some (sequent_after_eliminations, environment_describing_types_of_free_variables).
*)
let elim_fv_in_seq_for_bapa ((asms,conc) : sequent) (env:mapVarType) : ((sequent*mapVarType) option) =
  let rec substitute_and_elimfree (var_to_replace:ident) (replacement:form) (fs_todo: form list) (fs_done: form list) (changing_conc:form) (smaller_env:mapVarType) : ((sequent*mapVarType) option) =
    let sb = subst_formlist_simplifying_for_bapa var_to_replace replacement in
    let new_fs_todo = sb fs_todo in
    let new_fs_done = sb fs_done in
    let new_smaller_env = MapOfVars.remove var_to_replace smaller_env in
    let new_changing_conc = subst_form_simplifying_for_bapa var_to_replace replacement changing_conc in
    elimfree new_fs_todo new_fs_done new_changing_conc new_smaller_env true true
  and elimfree (fs_todo: form list) (fs_done: form list) (changing_conc:form) (smaller_env:mapVarType) (totally_changed:bool) (possibly_simplified_current_round:bool) : ((sequent*mapVarType) option) =
    (match fs_todo with
        [] -> if possibly_simplified_current_round then elimfree fs_done [] changing_conc smaller_env true false
              else if totally_changed then Some ((fs_done, changing_conc),smaller_env) 
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
            | App (Const Seteq, [Var v1; Var v2]) ->
                if v1=v2 then
                  let new_smaller_env = if var_in_others v1 then smaller_env else MapOfVars.remove v1 smaller_env in
                  elimfree remaining_asms fs_done changing_conc new_smaller_env true possibly_simplified_current_round
                else
                  if var_in_others v1 then
                    if var_in_others v2 then substitute_and_elimfree v1 (Var v2) remaining_asms fs_done changing_conc smaller_env
                    else elimfree remaining_asms fs_done changing_conc (MapOfVars.remove v2 smaller_env) true possibly_simplified_current_round
                  else 
                    let env_without_v1 = MapOfVars.remove v1 smaller_env in
                    if var_in_others v2 then elimfree remaining_asms fs_done changing_conc env_without_v1 true possibly_simplified_current_round
                    else elimfree remaining_asms fs_done changing_conc (MapOfVars.remove v2 env_without_v1) true possibly_simplified_current_round
            | App (Const Eq, [Var v; rhs])
            | App (Const Eq, [rhs; Var v])
            | App (Const Iff, [Var v; rhs])
            | App (Const Iff, [rhs; Var v])
            | App (Const Seteq, [rhs; Var v])
            | App (Const Seteq, [Var v; rhs]) ->
                if isfree_var v rhs then 
		  elimfree remaining_asms (curr_asm::fs_done) changing_conc smaller_env totally_changed possibly_simplified_current_round
                else substitute_and_elimfree v rhs remaining_asms fs_done changing_conc smaller_env
            | Var v ->
                substitute_and_elimfree v FormUtil.mk_true remaining_asms fs_done changing_conc smaller_env
            | App(Const Not,[Var v]) ->
                substitute_and_elimfree v FormUtil.mk_false remaining_asms fs_done changing_conc smaller_env
            | _ -> elimfree remaining_asms (curr_asm::fs_done) changing_conc smaller_env totally_changed possibly_simplified_current_round
          )
    )
  in elimfree asms [] conc env false false

(** [remove_equals var_list frm]
    converts a list of variables var_list into a list without multiple variable occurences. Instead of further occurences of the same variable, fresh variables are introduced.
    Returns (new_var_list,new_frm), where new_var_list is the new list of variables without multiple occurences and new_frm is frm with appended equalities.
*)
let remove_equals (var_list:typedIdent list) (frm:form) : ((typedIdent list)*form) =
  (* [equalize_setOfVars var ty eq_class]
     returns a list of typed equalities between var and each member of the set of variables eq_class. *)
  let equalize_setOfVars (var:ident) (ty:typeForm) : (setOfVars -> (form list)) =
    let make_equality = if FormUtil.is_set_type ty then FormUtil.mk_eq else FormUtil.mk_seteq in
    (fun (eq_class:setOfVars) ->
      SetOfVars.fold (fun curr_var sofar_equalities -> 
	(make_equality ((TypedForm((Var var),ty)),(TypedForm((Var curr_var),ty))))::sofar_equalities) eq_class [])
  in
  (* [remove_equals_aux sofar_varlist eq_classes varlist_to_go]
     returns (new_tvl,frm) where new_tvl is a list that starts with a conversion of varlist_to_go and ends with a conversion of sofar_varlist 
     in such a way that new_tvl has no multiple occurences of the same variable. Instead, fresh variables are introduced instead of duplicates and
     the equalities that show what variables should have the same values are returned as the additonal list of formulas frm.
  *)
  let rec remove_equals_aux (sofar_varlist: typedIdent list) (eq_classes: (typeForm*setOfVars) MapOfVars.t) : (typedIdent list) -> ((typedIdent list) * form list) =
    function
      [] -> ((List.rev sofar_varlist),
	     (MapOfVars.fold
	       (fun var (ty,eq_class_of_var) sofar_equalities -> 
		 (List.rev_append (equalize_setOfVars var ty eq_class_of_var) sofar_equalities)) eq_classes []))
    | (x,ty)::xs -> 
      let (remaining_list,(eq_class_of_x:setOfVars))=
	List.fold_right (fun ((curr_var:ident),(curr_ty:typeForm)) ((done_list:typedIdent list),(sofar_eq_class:setOfVars)) -> 
	  if curr_var=x then 
	    if FormUtil.equal_types ty curr_ty then 
	      let new_var = Util.fresh_name curr_var in
	      let eq_class = SetOfVars.add new_var sofar_eq_class in
	      (((new_var,curr_ty)::done_list),eq_class)
	    else failwith ("remove_equals_aux: in the variable list "^(PrintForm.wr_tuple var_list)^", the variable  "^x^" occurs with different types "^(PrintForm.string_of_type ty)^" and "^(PrintForm.string_of_type curr_ty)^".\n")
	  else (((curr_var,curr_ty)::done_list),sofar_eq_class)
	) xs ([],SetOfVars.empty) in
      let new_eq_classes = MapOfVars.add x (ty,eq_class_of_x) eq_classes
      in remove_equals_aux ((x,ty)::sofar_varlist) new_eq_classes remaining_list
  in 
  let (new_varlist,equalities) = remove_equals_aux [] (MapOfVars.empty) var_list in
  (new_varlist, (FormUtil.smk_and (frm::equalities)))

(** subset_relations_between_two_comprehensions {y. f1} {z. f2} 
    returns 
    Some (f1_sub_f2,f2_sub_f1), where for i!=j the formula fi_sub_fj is equivalent to
      (forall x . fi(x) => fj(x)), if the types of the two sets are the same, or if both sets are empty, and
    None, if the types of the two sets are different
*)
let subset_relations_between_two_comprehensions form1 form2 =
  match (form1,form2) with 
      ((Binder(Comprehension,[],bf1)),(Binder(Comprehension,[],bf2))) (* This case should not really occur *) -> Some (FormUtil.mk_true, FormUtil.mk_true)
    | ((Binder(Comprehension,[(v1,t1)],bf1)),(Binder(Comprehension,[(v2,t2)],bf2))) when (v1=v2 && (FormUtil.equal_types t1 t2)) -> 
        Some (Binder(Forall,[(v1,t1)],App(Const Impl,[bf1;bf2])),
	      Binder(Forall,[(v1,t1)],App(Const Impl,[bf2;bf1])))
    | ((Binder(Comprehension,[(v1,t1)],bf1)),(Binder(Comprehension,[(v2,t2)],bf2))) when v1=v2 -> None
    | ((Binder(Comprehension,[(v1,t1)],bf1)),(Binder(Comprehension,[(v2,t2)],bf2))) when FormUtil.equal_types t1 t2 -> 
	let (new_var,new_bf1,new_bf2)=
	  if isfree_var v1 bf2 then 
	    if isfree_var v2 bf1 then 
	      let name = Util.fresh_name (v1^v2) in 
	      let sbst = MapOfVars.add v1 (Var name) (MapOfVars.add v2 (Var name) MapOfVars.empty) in
	      (name, (subst sbst bf1), (subst sbst bf2))
	    else let sbst = MapOfVars.add v1 (Var v2) MapOfVars.empty in (v2,(subst sbst bf1),bf2)
	  else let sbst = MapOfVars.add v2 (Var v1) MapOfVars.empty in (v1,bf1,(subst sbst bf2))
	in Some (Binder(Forall,[(new_var,t1)],App(Const Impl,[new_bf1;new_bf2])),
		 Binder(Forall,[(new_var,t1)],App(Const Impl,[new_bf2;new_bf1])))
    | ((Binder(Comprehension,[(v1,t1)],bf1)),(Binder(Comprehension,[(v2,t2)],bf2))) -> None
    | ((Binder(Comprehension,tvl1,bf1)),(Binder(Comprehension,tvl2,bf2))) -> 
      let fv1 = fv_set bf1 in
      let fv2 = fv_set bf2 in
      let (tvl1,bf1) = remove_equals tvl1 bf1 in
      let (tvl2,bf2) = remove_equals tvl2 bf2 in
      (* gen_new_varlist remaining_vars1 remaining_vars2 sofar_vars sofar_sbst
	 generates a single list of bound variables out of two lists and prepends it to sofar_vars.
	 If both lists have different length or the variables at the same position have different types, it returns None.
	 If both lists have the same length, it returns Some (new_list,sbst1,sbst2) where new_list is a new list of variables, which contains as few fresh variables as possible,
	 and sbst1, sbst2 are substitutions of old variables by the fresh ones that extend sofar_sbst1 and sofar_sbst2, respectively. *)
      let rec gen_new_varlist remaining_vars1 remaining_vars2 sofar_vars sofar_sbst1 sofar_sbst2 =
	(match (remaining_vars1,remaining_vars2) with
	    ([],[]) -> Some ((List.rev sofar_vars),sofar_sbst1,sofar_sbst2)
	  | (_,[]) | ([],_) -> None
	  | (((curr_var1,curr_ty1)::xs1),((curr_var2,curr_ty2)::xs2)) ->
	    if FormUtil.equal_types curr_ty1 curr_ty2 then
	      if curr_var1 = curr_var2 then gen_new_varlist xs1 xs2 ((curr_var1,curr_ty1)::sofar_vars) sofar_sbst1 sofar_sbst2
	      else
		if (SetOfVars.mem curr_var1 fv2) || (List.mem_assoc curr_var1 xs2) then
		  if (SetOfVars.mem curr_var2 fv1) || (List.mem_assoc curr_var2 xs1) then
		    let new_name = Util.fresh_name (curr_var1^curr_var2) in
		    let new_sbst1 = MapOfVars.add curr_var1 (Var new_name) sofar_sbst1 in
		    let new_sbst2 = MapOfVars.add curr_var2 (Var new_name) sofar_sbst2 in
		    gen_new_varlist xs1 xs2 ((new_name,curr_ty1)::sofar_vars) new_sbst1 new_sbst2
		  else
		    let new_sbst1 = MapOfVars.add curr_var1 (Var curr_var2) sofar_sbst1 in
		    gen_new_varlist xs1 xs2 ((curr_var2,curr_ty2)::sofar_vars) new_sbst1 sofar_sbst2
		else
		  let new_sbst2 = MapOfVars.add curr_var2 (Var curr_var1) sofar_sbst2 in
		  gen_new_varlist xs1 xs2 ((curr_var1,curr_ty1)::sofar_vars) sofar_sbst1 new_sbst2
	    else None
	) in
      (match gen_new_varlist tvl1 tvl2 [] MapOfVars.empty MapOfVars.empty with
	  Some (new_varlist,sbst1,sbst2) -> 
	    let new_bf1 = subst sbst1 bf1 in
	    let new_bf2 = subst sbst2 bf2 in
	    Some ((Binder(Forall,new_varlist,App(Const Impl,[new_bf1;new_bf2]))),
		  (Binder(Forall,new_varlist,App(Const Impl,[new_bf2;new_bf1]))))
	| None -> None)
    | _ -> failwith ("subset_relations_between_two_comprehensions has to receive a pair of comprehensions, but it has received ("^(PrintForm.string_of_form form1)^"\n,"^(PrintForm.string_of_form form2)^".\n")

(** [simplify_sequent_wo_set_compr sq options]
    where sq is a seuqent and options control the decision procedure calls,
    returns
    Some true if the sequent could be shown to be valid,
    Some false if the sequent could be shown to be unsatisfiable,
    None in all other cases.
*)
let simplify_sequent_wo_set_compr ((assumptions,consequence) as sq :sequent) (options:Common.options_t): bool option =
  (* if Decider.test_valid sq then Some true else *)
  (* let _ = Util.msg ("simplify_sequent_wo_set_compr started on\n"^(FormUtil.string_of_sequent sq)^".\nRunning CVC...\n") in *)
  (* let _ = Util.msg ("simplify_sequent_wo_set_compr started on\n"^(MlPrintForm.string_of_sequent sq)^".\n") in *)
  (* let res= *)
  (match SmtCvcl.cvcl_prove false sq options with
      Some true ->
	(* let _ = Util.msg "CVC succeeded.\n" in *)
	Some true
    | _ -> 
	(* let _ = Util.msg "CVC failed.\nRunning Z3...\n" in *)
        (match SmtCvcl.z3_prove false sq options with
	 Some true ->
	   (* let _ = Util.msg "Z3 succeeded.\n" in *)
	   Some true
	  | _ -> (*let _ = Util.msg "Z3 failed.\n" in *)
		 None))
  (* in 
  let _ = Util.msg ("simplify_sequent_wo_set_compr finished with "^(match res with Some true -> "true" | Some false -> "false" | None -> "none")^".\n") in
  res *)


(** [subset_relations_between_fresh_setsymb assumptions bindings options]
    returns a list of formulas, where each formula is a (possibly negated) subset inclusion between those set variables whose corresponding sets actually satisfy (resp. never satisfy) the subset relation.
    The assumptions under which the subset inclusions hold or not hold are given as a parameter, 
    as well as the bindings of set variables to their definitions and the decision procedure options.
*)
let subset_relations_between_fresh_setsymb (assumptions: form list) (bindings:mapFormVar) (options:Common.options_t): form list =
  let _, res_rel =
    MapOfForms.fold (fun formula1 (symbol1,type1) (bindings_to_go,sofar_relations1) -> 
      let remaining_bindings=MapOfForms.remove formula1 bindings_to_go in
      (remaining_bindings,
       (MapOfForms.fold (fun formula2 (symbol2,type2) sofar_relations2 ->
	 if FormUtil.equal_types type1 type2 then
	   match subset_relations_between_two_comprehensions formula1 formula2 with
	       Some (f1_sub_f2,f2_sub_f1) -> 
		 let sq12:sequent = (assumptions,f1_sub_f2) in
		 let sq21:sequent = (assumptions,f2_sub_f1) in
		 let symb1_typed = FormUtil.mk_typedform(FormUtil.mk_var symbol1, type1) in
		 let symb2_typed = FormUtil.mk_typedform(FormUtil.mk_var symbol2, type2) in
		 (match simplify_sequent_wo_set_compr sq12 options with
		     Some true -> 
		       (match simplify_sequent_wo_set_compr sq21 options with
			   Some true -> ((FormUtil.mk_seteq (symb1_typed,symb2_typed))::sofar_relations2)
			 | Some false -> ((FormUtil.mk_subset(symb1_typed,symb2_typed))::sofar_relations2)
			 | None -> ((FormUtil.mk_subseteq(symb1_typed,symb2_typed))::sofar_relations2))
		   | Some false ->
		     (match simplify_sequent_wo_set_compr sq21 options with
			 Some true -> ((FormUtil.mk_subset (symb2_typed,symb1_typed))::sofar_relations2)
		       | Some false -> ((FormUtil.mk_not (FormUtil.mk_subseteq(symb1_typed,symb2_typed)))::
					   ((FormUtil.mk_not (FormUtil.mk_subseteq(symb2_typed,symb1_typed)))::
					       sofar_relations2))
		       | None -> ((FormUtil.mk_not (FormUtil.mk_subseteq(symb1_typed,symb2_typed)))::sofar_relations2))
		   | None ->
		     (match simplify_sequent_wo_set_compr sq21 options with
			 Some true -> ((FormUtil.mk_subseteq (symb2_typed,symb1_typed))::sofar_relations2)
		       | Some false -> ((FormUtil.mk_not (FormUtil.mk_subseteq (symb2_typed,symb1_typed)))::sofar_relations2)
		       | None -> sofar_relations2))
	     | None -> sofar_relations2
	 else sofar_relations2)
	  remaining_bindings sofar_relations1))
    ) bindings (bindings,[])
  in res_rel
    
(** membership_relations_between_a_freevar_and_a_freshsetsymb simple_var simple_ty set_form set_ty
    returns Some(f_in,f_not_in), where f_in is equivalent to "simple_var in set_form" and f_not_in is equivalent to "simple_var not in set_form", and set_form is a set comprehension over single elements (not over tuples)
    returns None, if set_form is a set comprehension over tuples,
    fails, if set_form is not a set comprehension.
*)
let membership_relations_between_a_freevar_and_a_freshsetsymb (simple_var:ident) (simple_ty:typeForm) (set_form:form) (set_ty:typeForm) =
  (*
  let _ = Util.msg ("membership_relations_between_a_freevar_and_a_freshsetsymb started with "^simple_var^" :: "^(PrintForm.string_of_type simple_ty)^" and "^(PrintForm.string_of_form set_form)^" :: "^(PrintForm.string_of_type set_ty)^".\n") in
  let res = *)
    match set_form with
	Binder(Comprehension, [], bf) -> Some(FormUtil.mk_bool false, FormUtil.mk_bool true)
      | Binder(Comprehension, [(x,x_ty)], bf) when FormUtil.equal_types x_ty simple_ty ->
          let sbst = MapOfVars.add x (FormUtil.mk_typedform ((FormUtil.mk_var simple_var),simple_ty)) MapOfVars.empty in
          let new_bf = subst sbst bf in
          Some (new_bf, (FormUtil.smk_not new_bf))
      | Binder(Comprehension, tvl, bf) -> None
      | _ -> failwith ("membership_relations_between_a_freevar_and_a_freshsymb: expected a set formula, but received "^(PrintForm.string_of_form set_form))
  (* in
  let _= Util.msg ("membership_relations_between_a_freevar_and_a_freshsetsymb finished with "^(
    match res with None -> "None" | Some (f1,f2) -> ((PrintForm.string_of_form f1)^", "^(PrintForm.string_of_form f2))
  )^".\n") in
  res *)

(** [membership_relations_between_freevars_and_freshsymb assumptions bindings options]
    returns a list of formulas, where each formula is a (possibly negated) membership relation between a variable that occurs freely in the assumptions and a set variable from bindings. Only such formulas are returned whose corresponding expanded definition holds. 
    The decision procedure parameters are given in options. *)
let membership_relations_between_freevars_and_freshsymb (assumptions: form list) (te:mapVarType) (bindings:mapFormVar) (options:Common.options_t): form list =
  let fv_of_asms = typed_fv_set_of_formlist assumptions te in
  MapOfForms.fold (fun frm (set_symb,set_ty) sofar_relations1 -> 
    let typed_setSymb = FormUtil.mk_typedform ((FormUtil.mk_var set_symb), set_ty) in
    MapOfVars.fold (fun simple_var simple_ty sofar_relations2 -> 
      if is_type_a_set_of set_ty simple_ty then
	match membership_relations_between_a_freevar_and_a_freshsetsymb simple_var simple_ty frm set_ty with
	    Some (f_in,f_not_in) -> 
	      let typed_simple = FormUtil.mk_typedform ((FormUtil.mk_var simple_var), simple_ty) in
	      let simpl_in_setSymb = FormUtil.mk_elem (typed_simple,typed_setSymb) in
	      let simpl_not_in_setSymb = FormUtil.mk_not simpl_in_setSymb in
	      (match simplify_sequent_wo_set_compr (assumptions,f_in) options with
		  Some true -> (simpl_in_setSymb::sofar_relations2)
		| Some false -> (simpl_not_in_setSymb::sofar_relations2)
		| None -> 
		  (match simplify_sequent_wo_set_compr (assumptions,f_not_in) options with
		      Some true -> (simpl_not_in_setSymb::sofar_relations2)
		    | Some false -> (simpl_in_setSymb::sofar_relations2)
		    | None -> sofar_relations2))
	  | None -> sofar_relations2
      else sofar_relations2
    ) fv_of_asms sofar_relations1
  ) bindings []

(** [remove_toplevel_cardinalities_of_finite_comprehensions sq te options]
    where sq is a sequent, te is its type invironment, and opts gives the call options for the decision procedure, returns another sequent sq' such that
    sq'=>sq and sq' does not contain cardinalities of finite comprehensions unless under a binder. *)
let remove_toplevel_cardinalities_of_finite_comprehensions (((assumptions,conc):sequent) as sq) (te:mapVarType) (options:Common.options_t) : sequent =
  match extract_cardinalities_of_comprehensions_of_sequent sq with
      Some ((simpler_sq_asms,simpler_sq_cons),(approx_sq_asms,approx_sq_conc),bindings) ->
	let extended_approximate_assumptions = (simplify_form_for_bapa (FormUtil.mk_not approx_sq_conc))::approx_sq_asms in
	let new_relations = List.rev_append (subset_relations_between_fresh_setsymb extended_approximate_assumptions bindings options) (membership_relations_between_freevars_and_freshsymb extended_approximate_assumptions te bindings options) in
	((List.rev_append new_relations simpler_sq_asms),simpler_sq_cons)
    | None -> sq
