open Form
open FormUtil


(* This is a shorthand for printing debug messages for this module. *)
let debug_id : int = Debug.register_debug_module "PureListTranslation"
let debug_msg : (string -> unit) = Debug.debug_msg debug_id
let debug_is_on () : bool = Debug.debug_is_on debug_id


(*
  TODO: normalize to deal with null at cons(....cons(2,null)) neq (cons(...,2))
 *)

let tail = Var "tail"
let head = Var "head"
let lst = Var "lst"
let cons = Var "cons"
let str_cons = "cons"
let str_lst = "lst"

let str_lstofVars = "lstofVars"
let str_lstofVals = "lstofVals"
let str_lstwithSuffix = "lstwithSuffix"

let mlPrint = MlPrintForm.string_of_form
let fPrint = PrintForm.string_of_form


(* type hashVars = typedIdent FormHashtbl.t *)
type hasheLists = typedIdent FormHashtbl.t

let str_smt_reach3 = "smt_reach3"

(* due to type checking we deffine var smt_trigger for the different types of triggers*)
let smt_trigger_p = "smt_trigger_p"
let smt_trigger_o = "smt_trigger_o"
let smt_trigger_o_p = "smt_trigger_o_p"
let smt_trigger_p_p = "smt_trigger_p_p"



(* short hands *)
let mk_smt_reach3 fld u v w =
  App((Var str_smt_reach3),  [(fld); (u); (v); (w)]) 
    
let mk_smt_reach3_not fld u v w =
  mk_or([( mk_smt_reach3 fld u v w); 
	 mk_and( [(mk_smt_reach3 fld u v v) ; 
		  mk_not(mk_smt_reach3 fld u w w)])])

let mk_app_eq field t1 t2 = 
  mk_eq( App((field), [t1]), t2)


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
  in (* PrintForm.print_form f1; *) f1

(*
let addHashVar hashVars kvar =
  if (FormHashtbl.mem hashVars kvar) = false then
    let kvar1 = mk_var (Util.fresh_name (PrintForm.string_of_form kvar)) 
    and kvar2 = mk_var (Util.fresh_name (PrintForm.string_of_form kvar)) in
      FormHashtbl.add hashVars kvar (kvar1,kvar2) ;
      let (vvar1,vvar2) = FormHashtbl.find hashVars kvar in
	debug_msg ("\n var added..kvar: " ^ PrintForm.string_of_form kvar  ^
		    " var 1:" ^ MlPrintForm.string_of_form vvar1 ^ "...var 2: " ^
		    MlPrintForm.string_of_form vvar2)
*)

let addHashList hashLists klist =
  if (FormHashtbl.mem hashLists klist) = false then
    let klist1 = mk_var (Util.fresh_name "l") in 
      FormHashtbl.add hashLists klist klist1 ;
      let vvar1 = FormHashtbl.find hashLists klist in
	debug_msg ("\n var added..klist: " ^ PrintForm.string_of_form klist  ^
		     " list 1:" ^ MlPrintForm.string_of_form vvar1 ^ "\n " )


(* Transformations from pureLists to HOL LISBQ *)	  

let rec unfold_list hashLists var1 lst =
  debug_msg("\n unfolding list..." ^ mlPrint lst ^ "\n ");
  addHashList hashLists lst;
  let abslst1 = FormHashtbl.find hashLists lst in
    match lst with
      | App((Var str_cons),[(App((Const Tuple),[c; Const NullConst]))]) ->
	  let f1 =
	    mk_and [
	      mk_app_eq tail abslst1 mk_null;
	      mk_app_eq head abslst1 c;
	    ]
	  in
	    debug_msg("\n unfold_list: null reached... lstn" ^ mlPrint abslst1 );
	    (f1,abslst1) 
      | App((Var str_cons),[(App((Const Tuple),[c; (App(applst, [Var vx]) )]))]) 
	  (*when applst = lst*) ->
	  let x = mk_var vx in
	  debug_msg("\n unfolding list var x..." ^ mlPrint x ^ "\n ");
	  (*addHashVar hashVars x;
	  let absvar11,absvar12 = FormHashtbl.find hashVars var1 in 
	  let absvar21,absvar22 = FormHashtbl.find hashVars x in *)
	  let f1 =
	    mk_and [
	      mk_app_eq head abslst1 c;
	      mk_app_eq tail abslst1 x;
	      mk_smt_reach3 tail x mk_null mk_null; 
	      mk_smt_reach3 tail var1 x x
	      (*mk_eq (absvar12,absvar22);*)
	    ]
	  in
	    (f1,abslst1)
      | App((Var str_cons),[(App((Const Tuple),[c; lst2]))]) ->
	  debug_msg("\n unfolding list.... n list unfolding ");
	  addHashList hashLists lst2;
	  let abslst2 = FormHashtbl.find hashLists lst2 in
	  let f1,abslstn = unfold_list hashLists var1 lst2 in 
	  let f2 =
	    mk_and [
	      mk_app_eq tail abslst1 abslst2;
	      mk_app_eq head abslst1 c;
	      f1
	    ]
	  in
	    (f2,abslstn)
      | _ ->
	  debug_msg("failing on unfol_list......" ^ fPrint lst );
	  mk_app_eq tail mk_null mk_null, abslst1
	  (*	
		| App((Var str_cons),[(App((Const Tuple),[c1; Const c2]))]) ->
		
		
		
	  *)
	  
let unfold_eq_vars l1 l2 =  
  mk_and [
    mk_eq (l1,l2);
    mk_smt_reach3 tail l1 mk_null mk_null;
    mk_smt_reach3 tail l2 mk_null mk_null;
  ]
    
  (*  addHashVar hashVars l1 ;  
      addHashVar hashVars l2 ;
      let v11,v12 = FormHashtbl.find hashVars l1 and
      v21,v22 = FormHashtbl.find hashVars l2 
      in 
      mk_and [
      mk_eq (v11,v21) ;
      mk_eq (v12,v22) ;
      mk_app_eq tail v21 mk_null ;
      mk_smt_reach3 tail v11 v12 v12
      ]
  *) 


let unfold_eq_var_list hashLists var1 l2 = 
  addHashList hashLists l2;
  let lst1 = FormHashtbl.find hashLists l2 in
  let lsti, lstn = unfold_list hashLists var1 l2 in 
  mk_and [
    mk_smt_reach3 tail var1 mk_null mk_null;
    mk_eq (var1, lst1);
    lsti
  ]
(*
  addHashVar hashVars var1;
  addHashList hashLists l2;
  let v11,v1n = FormHashtbl.find hashVars var1 in
  let lst1 = FormHashtbl.find hashLists l2 in
  let lsti, lstn = unfold_list hashLists var1 l2 in 
  let f1 =
  mk_and [
  mk_eq (var1, l2);
  lsti
  ]
  in
  f1 *)
      
      (*    mk_and [
	    mk_smt_reach3 tail v11 v1n v1n ; 
	    mk_app_eq tail v1n mk_null ;
	    mk_eq (v11,lst1) ;
	    mk_eq (v1n,lstn) ;
	    lsti
	    ]
      *)

let unfold_eq hashLists lhs rhs =
  debug_msg("\n Equality found... \n lhs: " ^ MlPrintForm.string_of_form lhs ^ " \n "
	    ^ "rhs: " ^ MlPrintForm.string_of_form rhs ^ "\n") ;
  match lhs with 
    | App (lstvar1,[x]) 
	when lstvar1 = lst -> 
	(match rhs with
	  | App (lstvar2,[y]) 
	      when lstvar2 = lst ->
	      debug_msg ( "\n found equality of Lists... \n" 
			  ^ "lhs: " ^ MlPrintForm.string_of_form lhs) ;
		unfold_eq_vars x y
	  | App ((Var "cons"),[flst]) ->
	      debug_msg ( "\n found equality of var = list... \n" 
			  ^ "lhs: " ^ MlPrintForm.string_of_form lhs) ;
	      unfold_eq_var_list hashLists x rhs
	  | _ -> mk_eq(lhs,rhs))
    | _ ->  mk_eq(lhs,rhs)

	
	
let unfold_neq hashLists lhs rhs =
  debug_msg("");
  mk_eq (lhs, rhs)

let unfold_suffix_vars l1 l2 =
  mk_and [
    mk_smt_reach3 tail l1 l2 l2
  ]

(*  addHashVar hashVars l1 ;  
  addHashVar hashVars l2 ;
  let v11,v12 = FormHashtbl.find hashVars l1 and
    v21,v22 = FormHashtbl.find hashVars l2 
    in
    mk_and [
    mk_smt_reach3 tail v11 v12 v12;
    mk_smt_reach3 tail v21 v22 v22;
    mk_smt_reach3 tail v11 v21 v21;
    mk_eq (v12,v22);
      mk_app_eq tail v12 mk_null
    ]
*)

let unfold_suffix hashLists f =
  match f with 
      | App (Var v, [Binder (Lambda, [_; _], p); par1; par2])
      | App (TypedForm (Var v, _), [Binder (Lambda, [_; _], p); par1; par2])
	  when v = str_rtrancl -> 
	  debug_msg ("\n found: rtrancl_pt...\n " ^ MlPrintForm.string_of_form f ^ "\n");
	    (match par1 with
	      | App (lstvar1,[x]) 
		  when lstvar1 = lst -> 
		  (match par2 with
		     | App (lstvar2,[y]) 
			 when lstvar2 = lst ->
			 debug_msg ( "\n found suffix of Lists... \n" 
				     ^ "par2: " ^ MlPrintForm.string_of_form par2) ;
			   unfold_suffix_vars x y
(*		     | App ((Var "cons"),[flst]) ->
		     debug_msg ( "\n found equality of var = list... \n" 
		     ^ "lhs: " ^ MlPrintForm.string_of_form lhs) ;
		     unfold_eq_var_list hashVars hashLists x rhs
*)
		     | _ -> 
			 debug_msg ( "\n could not handle par2: " 
				     ^ MlPrintForm.string_of_form par2); f)
	      | _ ->  
		  debug_msg ( "\n could not handle par1: " 
			      ^ MlPrintForm.string_of_form par1); f)
      | _ -> debug_msg ( "\n could not handle: rtrancl_pt...\n  " );  f
	  
	  

	  
let rewrite_rtrancl f encTriggers = 
    debug_msg ( " \n Begining pureList  rewriting ...............\n " 
	      ^ MlPrintForm.string_of_form f ^ "\n"
	      ^ PrintForm.string_of_form f ^ "\n") ;
  let hashLists = FormHashtbl.create 0
  in
  let rec rewrite_to_smt_reach3 f2 =
    let f3 = strip_types f2 
    in
    match f3 with 
      | App (Var v, [Binder (Lambda, [_; _], p); par1; par2])
      | App (TypedForm (Var v, _), [Binder (Lambda, [_; _], p); par1; par2])
	  when v = str_rtrancl -> unfold_suffix hashLists f3 
      | App (Const Not, [App (Const Eq, [lhs; rhs])] ) 
	-> unfold_neq hashLists lhs rhs       
      | App (Const Eq, [lhs; rhs]) 
	-> unfold_eq hashLists lhs rhs
	  
      | App(f, fs) -> (App(rewrite_to_smt_reach3 f, List.map rewrite_to_smt_reach3 fs))
      | TypedForm(f, t) ->  (TypedForm(rewrite_to_smt_reach3 f, t))      
      | Binder(b, tidlst, f) -> (Binder(b,tidlst, rewrite_to_smt_reach3 f))
      |	_ -> f3
  in 
  let f1 = rewrite_to_smt_reach3 f 
  in 
    debug_msg ( "\n after rewrite_to_smt_reach3... \n" 
		^ MlPrintForm.string_of_form f1 ^ "\n" 
		^ PrintForm.string_of_form f1 ^ "\n" );
    let encode_axioms f fld_lst = 
      let tp = mk_object_type and tp_b = mk_bool_type 
			      and t =(Var "t") 
			      and t0 = (Var "t0") 
			      and t1 = (Var"t1") 
			      and t2 = (Var "t2") 
			      and t3 = (Var "t3") 
      in
     
      (* AXIOMS without trigges *) 	
      let ax_transitive1 fld = (Binder(
				  Forall,
				  [ ("t1",tp); ("t2",tp); ("t3",tp) ], 
				  (mk_impl(
				     mk_and([mk_smt_reach3 fld t1 t2 t2 ;
					     mk_smt_reach3 fld t2 t3 t3]), 
				     mk_smt_reach3 fld t1 t3 t3)) )) 
      in
      let ax_transitive2 fld = (Binder(
				  Forall,
				  [ ("t",tp); ("t0",tp); ("t1",tp); ("t2",tp) ], 
				  (mk_impl(
				     mk_and([mk_smt_reach3 fld t0 t1 t2 ; 
					     mk_smt_reach3 fld t1 t t2]), 
				     mk_and([mk_smt_reach3 fld t0 t1 t ; 
					     mk_smt_reach3 fld t0 t t2]))))) 
      in
      let ax_transitive3 fld = (Binder(
				  Forall,
				  [ ("t",tp); ("t0",tp); ("t1",tp); ("t2",tp) ], 
				  (mk_impl( 
				     mk_and([mk_smt_reach3 fld t0 t1 t2 ;
					     mk_smt_reach3 fld t0 t t1]), 
				     mk_and([mk_smt_reach3 fld t0 t t2 ; 
					     mk_smt_reach3 fld t t1 t2]))))) 
      in
      let ax_order1 fld = (Binder(
			     Forall,
			     [ ("t1",tp); ("t2",tp); ("t3",tp) ], 
			     (mk_impl( 
				mk_and([mk_smt_reach3 fld t1 t2 t2 ; 
					mk_smt_reach3 fld t1 t3 t3]), 
				mk_or([mk_smt_reach3 fld t1 t2 t3 ; 
				       mk_smt_reach3 fld t1 t3 t2]))))) 
      in
      let ax_order2 fld = (Binder(
			     Forall,
			     [ ("t1",tp); ("t2",tp); ("t3",tp) ], 
			     (mk_impl( 
				mk_smt_reach3 fld t1 t2 t3, 
		                mk_and([
					 mk_smt_reach3 fld t1 t2 t2 ; 
					 mk_smt_reach3 fld t2 t3 t3]))))) 
      in
      let ax_reflexive fld = (Binder(
				Forall,
				[ ("t",tp) ], 
				( mk_smt_reach3 fld t t t ))) 
      in
      let ax_sandwich fld =  (Binder(
				Forall,
				[ ("t1",tp); ("t2",tp) ], 
				(mk_impl( 
				   mk_smt_reach3 fld t1 t2 t1, 
				   mk_eq(t1, t2) )))) 
      in
      let ax_cycle fld =  (Binder(
			     Forall,
			     [ ("t1",tp); ("t2",tp) ], 
			     (mk_impl( 
				mk_and([ mk_eq( (App(fld, [t1])), t1) ;
					 mk_smt_reach3 fld t1 t2 t2]),  
				mk_eq(t1, t2)  )) )) 
      in
      let ax_step fld =  (Binder(
			    Forall,
			    [ ("t",tp) ], 
			    (mk_smt_reach3 fld t (App(fld, [t])) (App(fld, [t])) ) ))  
      in
      let ax_reach fld = (Binder(
			    Forall,
			    [ ("t1",tp); ("t2",tp) ], 
			    (mk_impl( 
			       mk_smt_reach3 fld t1 t2 t2 , 
			       mk_or([ mk_eq(t1,t2) ; 
				       mk_smt_reach3 fld t1 (App(fld, [t1])) t2]))))) 
      in 
      let ax_null fld = mk_eq (App (fld, [mk_null]), mk_null) 
      in
      let ax_pure_null fld = 
	(Binder(
	   Forall,
	   [("t1",tp)], 
	   (mk_smt_reach3 fld t1 mk_null mk_null)))
      in
      let ax_pureList fld fld2 =
	(Binder(
	   Forall,
	   [ ("t1",tp); ("t2",tp) ], 
	   (mk_impl( 
	      mk_and[
		(mk_app_eq fld t1 (App(fld,[t2]))); 
		(mk_app_eq fld2 t1 (App(fld2,[t2])))],
	      mk_eq(t1,t2)))))
      in 
      let axioms fld = 
	mk_and
	  [ax_reach fld;
	   ax_step fld;
	   ax_cycle fld;
	   ax_sandwich fld;
	   ax_reflexive fld;
	   ax_order2 fld;
	   ax_order1 fld;
	   ax_transitive3 fld;
	   ax_transitive2 fld;
	   ax_transitive1 fld;
	   ax_null fld;
	   ax_pure_null fld;
	   ax_pureList fld head;
	 ]
      in


      (*AXIOMS with triggers *)	
      (* avoiding trigges with contain equalities mk_eq( (App(fld, [t1])), t1) z3 complains  *)

      let ax_transitive1_tr fld = (Binder
				     (Forall,
				      [ ("t1",tp); ("t2",tp); ("t3",tp) ],  
				      App(Var smt_trigger_p_p,
					  [ (mk_impl( 
					       mk_and([
							mk_smt_reach3 fld t1 t2 t2 ; 
							mk_smt_reach3 fld t2 t3 t3]),
					       mk_smt_reach3 fld t1 t3 t3)) ; 
					    mk_smt_reach3 fld t1 t2 t2 ; 
					    mk_smt_reach3 fld t2 t3 t3 ] ))) 
      in
      let ax_transitive2_tr fld = (Binder(
				     Forall,
				     [ ("t",tp); ("t0",tp); ("t1",tp); ("t2",tp) ], 
				     App(Var smt_trigger_p_p,
					 [ (mk_impl( mk_and([
							      mk_smt_reach3 fld t0 t1 t2 ;
							      mk_smt_reach3 fld t1 t t2]), 
						     mk_and([
							      mk_smt_reach3 fld t0 t1 t ; 
							      mk_smt_reach3 fld t0 t t2]))); 
					   mk_smt_reach3 fld t0 t1 t2 ; 
					   mk_smt_reach3 fld t1 t t2 ] ))) 
      in
      let ax_transitive3_tr fld = (Binder
				     (Forall,
				      [ ("t",tp); ("t0",tp); ("t1",tp); ("t2",tp) ], 
				      App(Var smt_trigger_p_p,
					  [ (mk_impl( 
					       mk_and([mk_smt_reach3 fld t0 t1 t2 ; 
						       mk_smt_reach3 fld t0 t t1]), 
					       mk_and([mk_smt_reach3 fld t0 t t2 ; 
						       mk_smt_reach3 fld t t1 t2]))) ; 
					    mk_smt_reach3 fld t0 t1 t2 ; 
					    mk_smt_reach3 fld t0 t t1 ] ))) 
      in
      let ax_order1_tr fld = (Binder(
				Forall,
				[ ("t1",tp); ("t2",tp); ("t3",tp) ], 
				App(Var smt_trigger_p_p,
				    [ (mk_impl( 
					 mk_and([mk_smt_reach3 fld t1 t2 t2 ; 
						 mk_smt_reach3 fld t1 t3 t3]), 
					 mk_or([mk_smt_reach3 fld t1 t2 t3 ; 
						mk_smt_reach3 fld t1 t3 t2]))) ;
				      mk_smt_reach3 fld t1 t2 t2 ; 
				      mk_smt_reach3 fld t1 t3 t3 ] ))) 
      in
      let ax_order2_tr fld = (Binder(
				Forall,
				[ ("t1",tp); ("t2",tp); ("t3",tp) ], 
				App(Var smt_trigger_p,
				    [ (mk_impl( 
					 mk_smt_reach3 fld t1 t2 t3,
					 mk_and([mk_smt_reach3 fld t1 t2 t2 ; 
						 mk_smt_reach3 fld t2 t3 t3])));  
				      mk_smt_reach3 fld t1 t2 t3  ] ))) 
      in
      (* at the moment without a trigger *)
      let ax_reflexive_tr fld = (Binder(
				   Forall,
				   [ ("t",tp) ], 
				   ( mk_smt_reach3 fld t t t ))) 
      in
      let ax_sandwich_tr fld =  (Binder(
				   Forall,
				   [ ("t1",tp); ("t2",tp) ],  
				   App(Var smt_trigger_p,
				       [ (mk_impl( 
					    mk_smt_reach3 fld t1 t2 t1, 
					    mk_eq(t1, t2) )) ; 
					 mk_smt_reach3 fld t1 t2 t1  ] ))) 
      in
      let ax_cycle_tr fld =  (Binder(
				Forall,
				[ ("t1",tp); ("t2",tp) ], 
				App(Var smt_trigger_p, 
				    [ (mk_impl( mk_and([ mk_eq( (App(fld, [t1])), t1) ; 
							 mk_smt_reach3 fld t1 t2 t2]),  
						mk_eq(t1, t2)  )) ;   
				      mk_smt_reach3 fld t1 t2 t2 ] ))) 
      in   
      let ax_step_tr fld = (Binder(
			      Forall,
			      [ ("t",tp) ], 
			      (TypedForm(App(Var smt_trigger_o, 
					     [(mk_smt_reach3 fld t (App(fld, [t])) (App(fld, [t]))) ; 
					      (App(fld, [t])) ]),tp_b))))  
      in
	(* axiom ax_reach_tr is missing f(t_1) as antecedent *)
      let ax_reach_tr fld = (Binder(
			       Forall,
			       [ ("t1",tp); ("t2",tp) ],  
			       App(Var smt_trigger_o_p, 
				   [(mk_impl( 
				       mk_smt_reach3 fld t1 t2 t2 , 
				       mk_or([ mk_eq(t1,t2) ; 
					       mk_smt_reach3 fld t1 (App(fld, [t1])) t2]))) ;   
				    (App(fld, [t1])) ; 
				    mk_smt_reach3 fld t1 t2 t2  ] ))) 
      in 
	(*  let ax_pure_null_tr fld = 
	    (Binder(
	    Forall,
	   [("t1",tp)], 
	    App( Var smt_trigger_p, 
	    [(mk_smt_reach3 fld t1 mk_null mk_null) ;
	    (mk_smt_reach3 fld t1 mk_null mk_null) ])))
	    in
	    let ax_pureList_tr fld fld2 =
	    (Binder(
	    Forall,
	    [ ("t1",tp); ("t2",tp) ], 
	    App( Var smt_trigger_p_p, 
	    [(mk_impl( 
	    mk_and[(mk_app_eq fld t1 (App(fld,[t2]))); 
			   (mk_app_eq fld2 t1 (App(fld2,[t2])))],
	    mk_eq(t1,t2)));
	    (mk_app_eq fld t1 (App(fld,[t2])));
	    (mk_app_eq fld2 t1 (App(fld2,[t2])))
	    ])))
	    in *) 
      let axioms_trigger fld = 
	mk_and
	  [ax_step_tr fld; 
	   ax_reach_tr fld;
	   ax_cycle_tr fld;
	   ax_sandwich_tr fld;
	   ax_reflexive_tr fld;
	   ax_order2_tr fld;
	   ax_order1_tr fld;
	   ax_transitive3_tr fld;
	   ax_transitive2_tr fld;
	   ax_transitive1_tr fld;
	   ax_null fld;
	   ax_pure_null fld;
	   ax_pureList fld head;
	 ]
      in

      let encAxioms = 
	if encTriggers then
	  axioms_trigger
	else
	  axioms
      in
       (*generate a set of axioms for the given fields *)	  
      let rec axiom_sets fld_lst =
	match fld_lst with
	  | [] -> mk_true
	  | hd :: flds -> mk_and([axiom_sets flds ; encAxioms hd ])
      in
	(smk_impl (axiom_sets fld_lst,f)) 
    in
    let f2 = encode_axioms f1 [tail]
    in
    let f3 = smart_abstract_constructs [(Var str_smt_reach3, 1)] f2 
    in
      debug_msg ( "\n after smart_abstract_constructs... \n" 
		  ^ MlPrintForm.string_of_form f3 ^ "\n" 
		  ^ PrintForm.string_of_form f2 ^ "\n" ) ;
      f3


