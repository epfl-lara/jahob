open Form
open FormUtil

(* This is a shorthand for printing debug messages for this module. *)
let debug_id : int = Debug.register_debug_module "RtranclTreeTranslation"
let debug_msg : (string -> unit) = Debug.debug_msg debug_id
let debug_is_on () : bool = Debug.debug_is_on debug_id


let str_parent_reach = "parent_reach"
let str_rtrancl_reach = "rtrancl_reach"
let str_fol_reach = "fol_reach"
let str_bp_q_func = "bp_q"

(* TODO:  
   - remove all warnings    
   - make sure that translation only applies to the current fields 
     (conjunctions under rtrancl_pt)
   - add smt_trigger obj obj
*)

let v_str = Util.fresh_name "v"
let w_str = Util.fresh_name "w"
let v_var = mk_var v_str
let w_var = mk_var w_str
let tp = mk_object_type 
let mk_predTrue = Binder(Lambda, [(v_str,tp); (w_str,tp)],mk_true)
let fields = ref []
let pFunc = ref (mk_var "p")
let pPreds = ref [(mk_predTrue)]
let t =mk_var (Util.fresh_name "t") and t1 = mk_var (Util.fresh_name "t1")
and t2 = mk_var (Util.fresh_name "t2") and t3 = mk_var (Util.fresh_name "t3")

(* type pTreeTuple =  *)
(*     { mutable parent: form list * form list list * form list list }  *)
(* let pTreeTuple : pTreeTuple = { parent=([],[[]],[[]]) } *)
let pTreeTable = ref []
let fail msg = raise (Invalid_argument msg)

let invert_pred predP =
  match predP with
    | Binder (Lambda, [(v,tp1); (w,tp2)], f) ->
      Binder (Lambda, [(w,tp1); (v,tp2)], f)
    |_ -> 	
      debug_msg ( " failing inverting lambda in ...\n " ^ 
		    PrintForm.string_of_form predP ^ "\n"); 
      predP


let reconstruct_field_writes f =
  let f1 =
    match normalize 3 f with
      | App (Const Or, [App (Const And, 
			     [App (Const Eq, [App (fld, [x1]); y1]); 
			      App (Const Not, [App (Const Eq, [lv1; x2])])]); 
			App (Const And, [App (Const Eq, [rv1; y2]); 
					 App (Const Eq, [lv2; x3])])])
	  when equal x1 x2 && equal x1 x3 && equal y1 y2 && equal lv1 lv2 ->
	mk_eq (App (mk_fieldWrite fld lv1 rv1, [x1]), y1)
      | _ -> f
  in 
  f1
    
let find_ptree f =
  let fs, g = sequent_of_form f in
  let ptree_decls, fs' = List.fold_left (fun (ptree_decls, fs') f ->
    match normalize 4 f with
      | App (Var ptree, [parent; App (Const ListLiteral, fields)]) when ptree = str_ptree ->
	let _ = 
	  List.iter 
	    (function 
	      | (Var fld) -> ()
	      | _ -> fail "Only atomic fields supported.")
	    (parent :: fields)
	in 
	let ptree_decls' = (parent, fields) :: ptree_decls in
	(* pTreeTuple.parent <- ( parent::((fun (x,_,_) -> x) pTreeTuple.parent), *)
	(* 		       fields ::((fun (_,x,_) -> x) pTreeTuple.parent), *)
	(* 		       [mk_true] ::((fun (_,_,x) -> x) pTreeTuple.parent)) ; *)
	let parents = List.map (fun (x,_,_)-> x) !pTreeTable in
	if not (List.exists (fun x -> FormUtil.equal x parent) parents) then
	  pTreeTable := (parent,fields,[mk_predTrue; 
					invert_pred mk_predTrue])::!pTreeTable;
	(ptree_decls', fs')
      | f' -> (ptree_decls, f :: fs')) 
    ([], []) fs
  in
  let _ = 
    match List.rev ptree_decls with
      | (parent, flds) :: ptree_decls' ->
	if ptree_decls' <> [] then 
	  Util.msg ("Found multiple ptree declarations in antecedent, " 
		    ^ "using the last one with parent field " 
		    ^ PrintForm.string_of_form parent ^"\n");
	fields := flds; 
	pFunc := parent;
      | [] -> fail "no ptree declarations found in antecedent"
  in 
  let f' = form_of_sequent (fs', g) in
  f'
    
let rewrite_rtrancl f encTriggers = 
  debug_msg ( " \n ===================Begining of parent_reach rewriting========= \n " 
	      ^ MlPrintForm.string_of_form f ^ "\n"
	      ^ PrintForm.string_of_form f ^ "\n") ;   
  let rec find_update cField pField= 
    match cField with 
      | (App((Const FieldWrite),[fld; x ; y])) -> find_update fld cField 
      | _ -> (cField, pField)
  in    
  let mk_parent_reach p u v =
    App((Var str_parent_reach),  [(p); (u); (v)]) 
  in
  let mk_rtrancl_reach p u v =
    App((Var str_rtrancl_reach),  [(p); (u); (v)]) 
  in
  let mk_fol_reach reach_field u v =
    App((Var reach_field),  [(u); (v)]) 
  in    
  let fldReads a b fld =
    mk_eq(App(fld,[a]) ,b) 
  in
  let mk_app_fld fld x = (App(fld, [x])) in
  let mk_app_fld_eq fld x y = fldReads x y fld in
  (* let mk_app_fld_neq fld x y = mk_not (mk_app_fld_eq fld x y) in *)
  let rec print_form_list flst =
    match flst with
      | [] -> ""
      | hd :: rest -> (PrintForm.string_of_form hd) 
	^ "\n" ^ print_form_list rest 
  in
  let beta_reducc f x y =
    match strip_types f with
      | (Binder (Lambda, [ (v, _); (w,_)], f1)) ->
  	let f2 =
  	  subst [(v, x); (w, y)] f1
  	in
	f2
      | _ -> f
  in
  let find_field f =
    match f with
      | (App((Const FieldWrite),[(f1); (p); (q)])) -> (f1, p, q)
      | _ ->  (f,mk_var "p", mk_var "q")
  in
  let add_predP predP =
    debug_msg ("adding predP... " ^ MlPrintForm.string_of_form predP); 
    if not (List.exists (fun x -> FormUtil.equal x predP) !pPreds) then
      pPreds := predP :: !pPreds
  in
  let rec rewrite_gamma fldSet mk_reach_fun fldxs f =  
    (* debug_msg ("rewriting with gamma in... "  *)
    (* 	       ^ PrintForm.string_of_form f ^ "\n") ; *)
    let rec wlp upd f =
      (* debug_msg ("rewriting wlp with fld ... " ^ PrintForm.string_of_form upd *)
      (* 		 ^  " and formula... " ^ PrintForm.string_of_form f ^ "\n" ) ; *)
      let (fld,p1,q1) = find_field upd in
      match f with
	| (App (Const Or, [f1 ; f2])) ->
      	  (App (Const Or, [wlp upd f1 ; wlp upd f2]))
	| (App (Const And, [f1 ; f2])) ->
      	  (App (Const And, [wlp upd f1; wlp upd f2]))
	| App((Var reach),  [(p); (x); (y)]) ->
  	  let predP1 =
  	    Binder (Lambda,
  		    [(v_str,tp); (w_str,tp)],
  		    wlp upd (beta_reducc p (v_var) (w_var)) )
  	  in
	  debug_msg ("rewriting wlp input predP... " 
		     ^ reach ^ " " 
		     ^ PrintForm.string_of_form p  
		     ^ " field f=" ^ MlPrintForm.string_of_form fld 
		     ^ "all fields: " ^ MlPrintForm.string_of_form (smk_and fldSet) 
		     ^  "\n" ) ;
  	  if List.exists (fun x -> x = (fld)) fldSet then
  	    let flds1 = List.filter (fun x -> x <> fld) fldSet in
  	    let predP2 =
  	      Binder (Lambda,
  		      [(v_str,tp); (w_str,tp)],
  		      smk_and([beta_reducc predP1 (v_var) (w_var);
  			       (smk_impl( mk_eq(v_var, p1) , 
					  smk_or(List.map (fldReads p1 (w_var)) flds1)
				))]))
  	    in
  	    (*TODO: big disjunct F*(P'',x,y) | F*(P',x,p) & F*(P'',q,y) & P'(p,q) *)
	    (* debug_msg ("predicate predP2... "  *)
	    (* 	     ^ PrintForm.string_of_form predP2 ^ "\n" ); *)
	    let disj1 = mk_reach_fun predP2 x y in
	    let conj1 = mk_reach_fun predP1 x p1 in
	    let conj2 = mk_reach_fun predP2 q1 y in
	    let conj3 = beta_reducc predP1 (p1) (q1) in
	    let fwlp = smk_or([disj1; smk_and([conj1; conj2; conj3 ])]) in
	    if reach = str_rtrancl_reach then begin
	      add_predP (invert_pred predP1); 
	      add_predP (invert_pred predP2)
	    end 
	    else begin
	      add_predP predP1; 
	      add_predP predP2
	    end;
	    fwlp
	  else   
	    begin
	      debug_msg ("case ~f:F ... \n " ) ; f
	    end
	| mk_true -> (* this is an all match, not just matching true! *) 
	  (* debug_msg ("matching f with true in wlp ... "  *)
	  (* 	     ^ PrintForm.string_of_form f ^ "\n" ) ;  *)
	  mk_true
    (* | _ ->  debug_msg ("failing matching in wlp... "  *)
    (* 			 ^ PrintForm.string_of_form f ^ "\n" ) ; f *)
    in
    match fldxs with 
      | [] -> f
      | hd :: rest -> 
	let fwlp = wlp hd f in 
	(* debug_msg ("\n after gamma in rewrite gamma... "  *)
	(*        ^ PrintForm.string_of_form fwlp ^ "\n" ) ; *)
	rewrite_gamma fldSet mk_reach_fun rest fwlp
  in
  let unfold_fldWrites fld =
    (* debug_msg ("unfold_fldWrites... "  *)
    (* 	       ^ PrintForm.string_of_form fld ^ "\n" ) ; *)
    match fld with 
      | (App((Const Eq),[(App(fldw,[x])); (y)])) ->
	let fldName,_ = find_update fldw fldw
	in
	let rec unfold_field fld =
	  match fld with 
	    | (App((Const FieldWrite),[flda; x ; y])) -> 
	      (App((Const FieldWrite),[fldName; x ; y])) :: (unfold_field flda )
	    | _ ->   []
	in
	unfold_field fldw
      | _  -> 	[]
  in
  let rec enlist_fields fldForm =
    match fldForm with
      | (App(Const Eq, [ls; rs])) as eq -> [eq]	
      | (App (Const Or, [flda ; fldForma])) 
      | (App (Const And, [flda ; fldForma])) -> flda :: (enlist_fields fldForma)
      | c -> debug_msg ("\n non matched fldForm case....  \n " 
			^ MlPrintForm.string_of_form c ) ; 
	[c]
  in
  let rec unfold_fields fldForms =
    match fldForms with
      | [] -> []
      | hd :: rest -> (unfold_fldWrites hd) @ (unfold_fields rest)
  in
  let lhs_of_eq f = 
    match f with 
      |(App((Const Eq),[lhs;rhs])) -> lhs
      | _ -> f
  in  
  let rec rewrite_to_rtrancl_reach f =
    match f with 
      | App (Var v, [Binder (Lambda, [_; _], p); par1; par2])
      | App (TypedForm (Var v, _), [Binder (Lambda, [_; _], p); par1; par2])
	  when v = str_rtrancl -> 
	debug_msg ("\n found: rtrancl_pt...\n " ^ MlPrintForm.string_of_form f ^ "\n");
	    let sub_f = strip_types (reconstruct_field_writes p) 	      
	    in
	    debug_msg ("matching subf... \n" ^ MlPrintForm.string_of_form sub_f ^ "\n" ) ;
	    (match sub_f with 
	      |(App((Const Eq),[(App(fldUpd,[_])); _ ])) as fldsForm ->
		let fldName,_ = find_update fldUpd fldUpd in
		debug_msg ("\n fieldName (if) ... \n "
			   ^ MlPrintForm.string_of_form fldName);
		if fldName = !pFunc then
		  begin 
		    let fldsArg = (unfold_fields (enlist_fields fldsForm)) in
		    let f4 = mk_parent_reach mk_predTrue par1 par2 in
		    debug_msg ("\n parent in rtrancl found ... \n " 
			       ^ PrintForm.string_of_form fldUpd
			       ^ "formula: " ^ PrintForm.string_of_form f4);
		    let f5 = rewrite_gamma [!pFunc] mk_parent_reach fldsArg f4 in
		    debug_msg ("\n after gamma ... "
			       ^ PrintForm.string_of_form f5 ) ; f5
		  end		  
		else
		  if List.exists (fun x -> x = (fldName)) !fields  then
		    begin
		      let fldsArg = (unfold_fields (enlist_fields fldsForm)) in
		      debug_msg ("found rtrancl without P predicate... " 
				 ^ PrintForm.string_of_form (smk_and (enlist_fields fldsForm)) 
				 ^ "\n" ^ "name_of_field " 
				 ^ PrintForm.string_of_form fldName
				 ^ "\n" ) ;
		      let f4 = mk_rtrancl_reach mk_predTrue par1 par2 in
		      let f5 = rewrite_gamma !fields mk_rtrancl_reach fldsArg f4 in
		      debug_msg ("\n after gamma ... "
				 ^ PrintForm.string_of_form f5 ) ; f5
		    end
		  else
		    begin
		      debug_msg ("field not in fields, skipping fieldName: " 
				 ^ PrintForm.string_of_form fldName ^ "\n");
		      f
		    end
	      | fldsForm ->
		let fldsArg = (unfold_fields (enlist_fields fldsForm)) in
		debug_msg ("found rtrancl conjunctions LOOK for fields... " 
			   ^ PrintForm.string_of_form (smk_and (enlist_fields fldsForm)) 
			   ^ "\n" ) ;
		let fldUpd = lhs_of_eq (List.hd (enlist_fields fldsForm)) in
		let fldName,_ = find_update fldUpd fldUpd in
		if List.exists (fun x -> x = (fldName)) !fields  then 
		  begin
		    let f4 = mk_rtrancl_reach mk_predTrue par1 par2 in
		    let f5 = rewrite_gamma !fields mk_rtrancl_reach fldsArg f4 in
		    debug_msg ("\n after gamma ... "
			       ^ PrintForm.string_of_form f5 ) ; f5
		  end
		else 
		  begin
		    debug_msg ("field not in fields, skipping fieldName: " 
			       ^ PrintForm.string_of_form fldName ^ "\n");
		    f
		  end
	    )
      | App(f, fs) -> (App(rewrite_to_rtrancl_reach f, List.map rewrite_to_rtrancl_reach fs))
      | TypedForm(f, t) ->  (TypedForm(rewrite_to_rtrancl_reach f, t))      
      | Binder(b, tidlst, f) -> (Binder(b,tidlst, rewrite_to_rtrancl_reach f))
      |	f -> f
  in 
  let rec rewrite_to_parent_reach f2 = 
    (* F*(P,x,y) <==>    x = y | *)
    (* 	(x ~= null & *)
    (* 	    (  (y = null & EX z. p(z) = null & P(z,null) & p*(P^{-1},z,x)) *)
    (* 		| (y ~= null & p*(P^{-1},y,x)) )) *)
    match f2 with 
      | App((Var reach),  [(p); (x); (y)]) when reach = str_rtrancl_reach ->
	debug_msg ( "\n found rtrancl reach, rewritting to parent reach...\n " ^
		      PrintForm.string_of_form f2 ^ "\n");
	let p2 = invert_pred p in
	let tp = mk_object_type in
	let z = mk_var (Util.fresh_name "z") in
	let conj2211 = mk_eq(y,mk_null) in
	(* let conj2212 = (App((Const FieldRead),[(!pFunc); (z); (mk_null)])) in *)
	let conj2212 = fldReads z mk_null !pFunc in
	let conj2213 = (beta_reducc p (z) (mk_null)) in
	let conj2214 = App((Var str_parent_reach), [(p2); (z); (x)]) in
	let conjQuant = 
	  let qf = smk_and([ conj2212; conj2213; conj2214]) in
	  if encTriggers then  begin
	    (* mk_exists (unvar z, tp, *)
	    (* 	       App (Var smt_trigger_obj,  *)
	    (* 		    [qf;App(!pFunc, [z])]))  *)
	    mk_exists (unvar z, tp, qf)
	  end
	  else 
	    mk_exists (unvar z, tp, qf)
	in

	let disj221 = smk_and([conj2211; conjQuant]) in
	let disj222 = smk_and([mk_neq(y,mk_null) ;
			       App((Var str_parent_reach),  [(p2); (y); (x)])])
	in
	let conj22 = smk_or([disj221; disj222]) in
	let conj21 = mk_neq(x,mk_null) in
	(* let conj2 = mk_and([conj21;conj22]) in *)
	let disj1 = mk_eq(x,y) in
	let disj2 = smk_and([conj21; conj22]) in
	let f3 = smk_or([disj1; disj2]) in
	debug_msg ( "after rewritting to parent reach...\n " ^
		      PrintForm.string_of_form f3 ^ "\n");
	f3
      | App(f, fs) -> (App(rewrite_to_parent_reach f, List.map rewrite_to_parent_reach fs))
      | TypedForm(f, t) ->  (TypedForm(rewrite_to_parent_reach f, t))      
      | Binder(b, tidlst, f) -> (Binder(b,tidlst, rewrite_to_parent_reach f))
      |	_ -> f2
  in

  let mk_univ_ax ids qf trgs trg_type =
    let list_ids = List.map (fun id -> (unvar id, tp)) ids      in
    let trg_qf = App(Var trg_type,  qf::trgs ) in
    match trgs with
      | [] -> Binder(Forall, list_ids, qf)
      | _  -> 
	if encTriggers then
	  Binder(Forall, list_ids, trg_qf)	  
	else
	  Binder(Forall, list_ids, qf)
  in

  let encode_axioms f predlst fol_reach parent flds = 
    (* and tp_b = mk_bool_type and t0 = (Var "t0")   *)
    (* let t =mk_var (Util.fresh_name "t") and t1 = mk_var (Util.fresh_name "t1") *)
    (* and t2 = mk_var (Util.fresh_name "t2") and t3 = mk_var (Util.fresh_name "t3") in *)
    (* let parent = !pFunc in *)
    (* let flds = !fields in *)
    let cust_mk_or f1 f2 = smk_or([f1;f2]) in
    let cust_mk_and f1 f2 = smk_and([f1;f2]) in
    (* let truePred = Binder(Lambda, [(unvar t1, tp); (unvar t2, tp)], mk_true) in *)
    let mk_p_reach x y = mk_fol_reach fol_reach x y in

    let ax_n_child =
      let ax_fc fld =
    	let trg1 = (mk_app_fld fld t) in
    	let qf = (smk_or([mk_app_fld_eq parent (mk_app_fld fld t) t ;
    			  mk_app_fld_eq fld t mk_null]))
    	in
    	mk_univ_ax [t] qf [trg1] smt_trigger_obj
      in
      let ax =
    	List.fold_left
    	  cust_mk_and
    	  mk_true
    	  (List.map ax_fc flds)
      in
      mk_comment " \n ax_n_child one conj per child field: \n " ax
    in
    let ax_parent =
      let trg1 = (mk_app_fld parent t) in
      let ax_par fld =
	mk_app_fld_eq fld (mk_app_fld parent t) t
      in
      let qf =
    	List.fold_right
    	  cust_mk_or
	  (List.map ax_par flds)
    	  (mk_app_fld_eq parent t mk_null)
      in
      let ax =
	mk_univ_ax [t] qf [trg1] smt_trigger_obj
      in
      mk_comment " \n ax_parent: \n " ax
    in
    (* let ax_parent1 = *)
    (*   let trg1 = (mk_app_fld parent t) in *)
    (*   let ax_par fld = *)
    (* 	mk_app_fld_eq fld t1 t2 *)
    (*   in *)
    (*   let qf = *)
    (* 	List.fold_right *)
    (* 	  cust_mk_or *)
    (* 	  (List.map ax_par flds) *)
    (* 	  (mk_app_fld_eq parent t mk_null) *)
    (*   in *)
    (*   let ax = *)
    (* 	mk_univ_ax [t] qf [trg1] smt_trigger_obj *)
    (*   in *)
    (*   mk_comment " \n ax_parent1: \n " ax *)
    (* in *)

    let ax_lrn_distinct =
      (* let mk_trgs term fld = (mk_app_fld fld term) in *)
      let rec mk_combine fld flst1 =
    	match flst1 with
    	  | [] -> mk_false
    	  | x :: xs ->
    	    smk_or([mk_and([mk_app_fld_eq fld t1 t2;
    			    mk_app_fld_eq x t1 t2]);
    		    mk_combine fld xs])
      in
      let rec combine_flds flst =
    	match flst with
    	  | [] -> mk_false
    	  | x :: xs ->
    	    smk_or( [(mk_combine x xs) ; (combine_flds xs)])
      in
      let antecedent = combine_flds flds in
      let consequent = mk_eq(t2,mk_null) in
      let ax =
    	if (List.length flds)<=1 then
    	  mk_true
    	else
    	  begin
	    (* let trgxs = List.map (mk_trgs t1) flds in *)
    	    let qf = smk_impl(antecedent, consequent) in
    	    mk_univ_ax [t1; t2] qf [] smt_trigger_obj
    	  end
      in
      mk_comment "\n ax_lrn_distinct: \n " ax
    in
    let ax_n_root =
      let ax_fr fld =
    	let trg1 = (mk_app_fld parent t1) in
	let antecedent =
    	  mk_and([mk_app_fld_eq parent t1 mk_null;
    		  mk_app_fld_eq fld t2 t1])
	in
	let consequent = mk_eq(t1,mk_null) in
    	let qf = mk_impl(antecedent,consequent) in
    	mk_univ_ax [t1; t2] qf [trg1] smt_trigger_obj
      in
      let ax =
    	List.fold_left
    	  cust_mk_and
    	  mk_true
    	  (List.map ax_fr flds)
      in
      mk_comment " \n ax_n_root one conj per child field: \n " ax
    in
    let ax_p_loop =
      let trg1 = (mk_app_fld parent t) in
      let ax =
    	let qf = smk_impl(mk_app_fld_eq parent t t,
    			  mk_eq(t,mk_null))
    	in
    	mk_univ_ax [t] qf [trg1] smt_trigger_obj
      in
      mk_comment "\n ax_p_loop: \n " ax
    in
    let ax_nullTerm =
      let ax =
    	let qf = mk_p_reach t mk_null  in
    	mk_foralls ([(unvar t, tp)], qf)
      in
      mk_comment "\n ax_nullTerm: \n " ax
    in
    let ax_refl =
      let ax =
    	let qf = mk_p_reach t t in
    	mk_foralls ([(unvar t, tp)], qf)
      in
      mk_comment "\n ax_refl: \n "  ax
    in
    let ax_trans =
      let trg1 = mk_p_reach t1 t2 in
      let trg2 = mk_p_reach t2 t3 in
      let antecedent =
    	mk_and([mk_p_reach t1 t2;
    		mk_p_reach t2 t3])
      in
      let consequent = mk_p_reach t1 t3
      in
      let ax =
    	let qf = smk_impl(antecedent,consequent) in
    	mk_univ_ax [t1;t2;t3] qf [trg1; trg2] smt_trigger_bool_bool
      in
      mk_comment "\n ax_trans: \n " ax
    in 
    let ax_antiSym =
      let trg1 = mk_p_reach t1 t2 in
      let trg2 = mk_p_reach t2 t1 in
      let antecedent =
    	mk_and([mk_p_reach t1 t2;
    		mk_p_reach t2 t1])
      in
      let consequent = mk_eq(t1,t2)
      in
      let ax =
    	let qf = smk_impl(antecedent,consequent)
    	in
    	mk_univ_ax [t1;t2] qf  [trg1; trg2] smt_trigger_bool_bool
      in
      mk_comment "\n ax_antiSym: \n "	  ax
    in
    let ax_total =
      let trg1 = mk_p_reach t1 t2 in
      let trg2 = mk_p_reach t1 t3 in
      let antecedent =
    	mk_and([mk_p_reach t1 t2;
    		mk_p_reach t1 t3])
      in
      let consequent =
    	smk_or([mk_p_reach t3 t2;
    		mk_p_reach t2 t3])
      in
      let ax =
    	let qf = smk_impl(antecedent,consequent) in
    	mk_univ_ax [t1;t2;t3] qf [trg1; trg2] smt_trigger_bool_bool
      in
      mk_comment "\n ax_total: \n " ax
    in
    let ax_p_step =
      let ax =
    	let trg1 = (mk_app_fld parent t) in
    	let qf = mk_p_reach t (mk_app_fld parent t)
    	in
    	mk_univ_ax [t] qf [trg1] smt_trigger_obj
      in
      mk_comment "\n p-step: \n " ax
    in
    let ax_unfold =
      let trg1 = mk_p_reach t1 t2 in
      let antecedent = mk_p_reach t1 t2 in
      let consequent =
    	smk_or([mk_eq(t1,t2);
    		mk_p_reach (mk_app_fld parent t1) t2])
      in
      let ax =
    	let qf = smk_impl(antecedent,consequent) in
    	mk_univ_ax [t1;t2] qf [trg1] smt_trigger_bool
      in
      mk_comment "\n ax_unfold: \n " ax
    in
    let ax_n_unfold =
      let trg1 = mk_p_reach t1 t2 in
      let antecedent = mk_p_reach t1 t2 in
      let consequent =
	smk_or 
	  (mk_eq (t1, t2) :: mk_eq (t2, mk_null) ::
	   List.map (fun fld -> 
    	     mk_and [mk_not (mk_eq (App (fld, [t2]), mk_null));
		     mk_p_reach t1 (App (fld, [t2]))]) flds)
      in
      let ax =
    	let qf = smk_impl (antecedent,consequent) in
    	mk_univ_ax [t1;t2] qf [trg1] smt_trigger_bool
      in
      mk_comment "\n ax_n_unfold: \n " ax
    in
    let axioms_P = 
      mk_and
	[
	  ax_n_child;
	  ax_parent;
	  ax_lrn_distinct;
	  ax_n_root;
	  ax_p_loop;
	  ax_nullTerm;
	  ax_refl;
	  ax_trans;
	  ax_antiSym;
	  ax_total;
	  ax_p_step;
	  ax_unfold;
	  ax_n_unfold
	]
    in  
    (* (\*generate a set of axioms for the given predicates *\)	   *)
    (* let rec axiom_sets predlst = *)
    (*   match predlst with *)
    (* 	| [] -> mk_true *)
    (* 	| hd :: rest -> smk_and([axiom_sets rest ; axioms_with_pred hd ]) *)
    (* in *)
    (* let all_axioms = smk_and([axiom_sets !pPreds; axioms_without_pred]) *)
    (* in *)
    debug_msg ( "\n axioms... \n" 
		^ PrintForm.string_of_form axioms_P ^ "\n" );
    (smk_impl (axioms_P,f)) 
  in
  let mk_bpFunctions pPreds =
    let mk_bpFunction x = mk_var 
      (Util.fresh_name (str_bp_q_func ^ string_of_int x ))   
    in
    let rec create_qTable preds =
      match preds with
	| [] -> []
	| x :: xs -> 
	  (x,mk_bpFunction (List.length preds)) :: create_qTable xs
    in
    let qTable = create_qTable pPreds 
    in
    let bpFunctions = List.map (fun (_,x) -> x) qTable 
    in
    debug_msg ( "\n bp preds --- functions: ... \n"
		^ (print_form_list pPreds)
  		^ (print_form_list bpFunctions)
		^ "\n" );
    qTable
  in
  let rec rewrite_to_fol_parent_reach qTable fol_reach_func f =
    match f with 
      | App((Var reach),  [(p); (x); (y)]) when reach = str_parent_reach ->
	debug_msg ( "\n found parent reach, rewritting to fol parent reach...\n " ^
		      PrintForm.string_of_form f ^ "\n");
	let bpFunc = List.assoc p qTable in
	let f2 =  mk_and ([ mk_fol_reach fol_reach_func x y ;
			    mk_fol_reach fol_reach_func y (mk_app_fld bpFunc x) ])
	in
	debug_msg ( "\n rewritten...\n " ^
		      PrintForm.string_of_form f2 ^ "\n");
	f2
      | App(f1, fs) -> (App(rewrite_to_fol_parent_reach qTable fol_reach_func f1,
			    List.map (rewrite_to_fol_parent_reach qTable fol_reach_func) fs))
      | TypedForm(f1, t) ->  
	(TypedForm(rewrite_to_fol_parent_reach qTable fol_reach_func f1, t))      
      | Binder(b, tidlst, f1) -> 
	(Binder(b,tidlst, rewrite_to_fol_parent_reach qTable fol_reach_func f1))
      |	_ -> f
  in

  let encode_Q_axioms f qTable fol_reach parent =
    let qPreds = List.map (fun (x,_) -> x) qTable in
    let mk_p_reach x y = mk_fol_reach fol_reach x y in
    let q_axioms qPred = 
      let bpFunc = List.assoc qPred qTable in 
      let ax_bpq_def1 = 
	let ax =
    	  let qf = mk_p_reach t (mk_app_fld bpFunc t)
    	  in
    	  mk_foralls ([(unvar t, tp)], qf)
	in
	mk_comment "\n ax_bpq_def1: \n " ax
      in
      let ax_bpq_def2 =
	let antecedent =
	  beta_reducc qPred 
	    (mk_app_fld bpFunc t) 
	    (mk_app_fld parent (mk_app_fld bpFunc t))
	in
	let consequent =
    	  mk_eq(mk_app_fld bpFunc t, mk_null)
	in
	let ax =
    	  let qf = smk_impl(antecedent,consequent) in
    	  mk_foralls ([(unvar t, tp)], qf)
	in
	mk_comment "\n ax_bpq_def2: \n " ax
      in
      let ax_bpq_def3 =
	let trg1 = mk_app_fld bpFunc t1 in
	let antecedent =
    	  smk_and([mk_p_reach t1 t2;
    		  mk_p_reach t2 (mk_app_fld bpFunc t1)])
	in
	let consequent =
    	  smk_or([beta_reducc qPred t2 (mk_app_fld parent t2);
    		  mk_eq(t2, mk_app_fld bpFunc t1)])
	in
	let ax =
    	  let qf = smk_impl(antecedent,consequent) in
    	  mk_univ_ax [t1;t2] qf [trg1] smt_trigger_obj
	in
	mk_comment "\n ax_bpq_def3: \n " ax
      in
      mk_and [
	ax_bpq_def1;
	ax_bpq_def2;
	ax_bpq_def3;
      ]
    in
    let all_Qaxioms = smk_and(List.map q_axioms qPreds) in
    debug_msg ( "\n Q axioms... \n" 
		^ PrintForm.string_of_form all_Qaxioms ^ "\n" );
    (smk_impl (all_Qaxioms,f)) 
  in
  let f0 = find_ptree f 
  in
  let rewrite_passes f (pTree,fldxs,pPredxs) =
    pFunc := pTree;
    fields := fldxs;
    pPreds := pPredxs;
    let f1 = rewrite_to_rtrancl_reach f in
    let f2 = rewrite_to_parent_reach f1 in
    let fol_reach = Util.fresh_name str_fol_reach  in
    let qTable = mk_bpFunctions !pPreds in
    let f3 = remove_comments (encode_axioms f2 !pPreds fol_reach pTree fldxs) in
    let f4 = rewrite_to_fol_parent_reach qTable fol_reach f3 in
    let f5 = remove_comments (encode_Q_axioms f4 qTable fol_reach pTree) in
    (* let f4 = smart_abstract_constructs [(Var str_parent_reach, 1)] f3 in *)
    f5
  in
  let f6 = List.fold_left rewrite_passes f0 !pTreeTable 
  in
  let pTrees = List.map (fun (x,_,_) -> x) !pTreeTable in
  debug_msg ( "\n after reach tree rewritting... \n"
  	      ^ " with pTrees: \n  "
  	      ^ (print_form_list pTrees)
  	      ^ PrintForm.string_of_form f6 ^ "\n" );
  f6
  (* let f1 = rewrite_to_parent_reach (rewrite_to_rtrancl_reach f0)  *)
  (* in *)
  (* debug_msg ( "\n after rewrite_to_parent_reach... \n"  *)
  (* 	      ^ PrintForm.string_of_form f1 ^ "\n" ); *)
  (* let f2 =  *)
  (*   debug_msg ( "\n P predicates... \n"  *)
  (* 		^ (print_form_list !pPreds) ^ "\n" ) ; *)
  (*   remove_comments (encode_axioms f1 !pPreds) *)
  (* in *)
  (* let f3 = smart_abstract_constructs [(Var str_parent_reach, 1)] f2  *)
  (* in *)
  (* debug_msg ( "\n after smart_abstract_constructs... \n"  *)
  (* 	      ^ PrintForm.string_of_form f3 ^ "\n" ); *)
  (* f3 *)
    
