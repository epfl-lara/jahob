open Form
open FormUtil


(* This is a shorthand for printing debug messages for this module. *)
let debug_id : int = Debug.register_debug_module "RtranclTranslation"
let debug_msg : (string -> unit) = Debug.debug_msg debug_id
let debug_is_on () : bool = Debug.debug_is_on debug_id

let str_smt_reach3 = "smt_reach3"

let fieldNames = ref []

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
let rewrite_rtrancl f encTriggers = 
  debug_msg ( " \n ===================Begining of smt_reach3  rewriting========= \n " 
	      ^ MlPrintForm.string_of_form f ^ "\n"
	      ^ PrintForm.string_of_form f ^ "\n") ;   
  let rec find_update cField pField= 
    match cField with 
      | (App((Const FieldWrite),[fld; x ; y])) -> find_update fld cField 
      | _ -> 
	  (* debug_msg ("\n fieldName: " ^ MlPrintForm.string_of_form cField 
	     ^ "fieldWrite: " ^ MlPrintForm.string_of_form pField) ; *)
	  if not (List.exists ( equal cField ) !fieldNames) then
	    fieldNames := cField :: !fieldNames;
          (cField, pField)
  in    
  let rec build_new_field cField fieldname goalField =
    debug_msg ("\n currentField:  "
	       ^ MlPrintForm.string_of_form cField 
	       ^ "fieldname: " ^ MlPrintForm.string_of_form fieldname 
               ^ "goalfield: " ^ MlPrintForm.string_of_form goalField) ;
    match cField with 
      | (App((Const FieldWrite),[fld; x ; y])) -> 
	  if cField = goalField then
	    fieldname
	  else
	    (App((Const FieldWrite),
		 [ (build_new_field fld fieldname goalField); x ; y]))   
	      (*	     build_new_field fld fieldname goalField *)
      | _ -> debug_msg ("\n no fieldWrites :  " ^ MlPrintForm.string_of_form cField ) ; cField
  in 
  let mk_smt_reach3 fld u v w =
    App((Var str_smt_reach3),  [(fld); (u); (v); (w)]) 
  in
  let mk_smt_reach3_not fld u v w =
    mk_or([( mk_smt_reach3 fld u v w); 
	   mk_and( [(mk_smt_reach3 fld u v v) ; 
		    mk_not(mk_smt_reach3 fld u w w)])])
  in
  let rec rewrite_gamma f2  = 
    (* debug_msg ("\n rewriting with gamma function .. \n" ^ MlPrintForm.string_of_form f2); *)
    (* TypedForm(App((Var "smt_reach3"),  [(vfld); (u); (v); (w)]),(TypeApp(TypeBool,[])))) *)
    match f2 with
      | App((Var str_smt_reach3),  [(vfld); (u); (v); (w)]) -> 
	  (*	debug_msg ("\n finding update.. " ) ; *)
	  let fieldName,innerFieldWrite = find_update vfld vfld in
	    ( match innerFieldWrite with
		| (App((Const FieldWrite),[fld1; p ; q])) ->
		    let newFW = build_new_field vfld fieldName innerFieldWrite 
		    in 
		    debug_msg ("\n innerFieldWrite.... " ^ MlPrintForm.string_of_form innerFieldWrite ) ;
		    debug_msg ("\n newField :  " ^ MlPrintForm.string_of_form newFW ) ; 	      
		    let disj1 = (mk_and([ mk_smt_reach3 newFW u v w ; 
					  mk_smt_reach3_not newFW u w p ])) 
		    in
		    let disj2 = (mk_and([ mk_neq(p,w) ; 
					  mk_and([mk_smt_reach3_not newFW u p w ; 
						  mk_and([mk_smt_reach3 newFW u v p ;
							  mk_smt_reach3_not newFW q w p])])])) 
		    in
		    let disj3 = (mk_and([ mk_neq(p,w) ; 
					  mk_and([mk_smt_reach3_not newFW u p w ; 
						  mk_and([mk_smt_reach3 newFW q v w ; 
							  mk_smt_reach3_not newFW q w p])])])) 
		    in
		    (*let disj1 = mk_and [mk_smt_reach3 newFW u v v; 
					mk_or [mk_smt_reach3 newFW v q q; mk_not (mk_smt_reach3 newFW u q q)]]
		    in
		    let disj2 = mk_and [mk_smt_reach3 newFW u p p; mk_smt_reach3 newFW q v v;
					mk_or [mk_not (mk_smt_reach3 newFW q p p); mk_smt_reach3 newFW v p p]]
		    in*)
		    let f5 = mk_or [disj1; disj2; disj3] in  
			(*  debug_msg ("\n rewriten with identity..:  \n" ^ MlPrintForm.string_of_form f5 ) ; *)
		    debug_msg ( "\n rewriten with identity... \n" ^  PrintForm.string_of_form f5 ^ "\n"  ) ; 
		    rewrite_gamma f5
		| _ -> f2	)    
      | App(Const And, [ls;rs]) -> mk_and([ rewrite_gamma ls ; rewrite_gamma rs  ]) 
      | App(Const Or, [ls;rs]) -> mk_or([ rewrite_gamma ls ; rewrite_gamma rs  ]) 
      | App(Const Not, [cs]) -> mk_not( rewrite_gamma cs )
      | App(Const Eq, [ls; rs]) as eq -> eq
      | c -> debug_msg ("\n non matched case....  \n " ^ MlPrintForm.string_of_form c ) ; c
  in
  let rec rewrite_to_smt_reach3 f3 =
    match f3 with 
      | App (Var v, [Binder (Lambda, [_; _], p); par1; par2])
      | App (TypedForm (Var v, _), [Binder (Lambda, [_; _], p); par1; par2])
	  when v = str_rtrancl -> 
	  debug_msg ("\n found: rtrancl_pt...\n " ^ MlPrintForm.string_of_form f3 ^ "\n");
	    let sub_f = strip_types (reconstruct_field_writes p)
	    in
	      (match sub_f with 
		 | App (Const Eq, [App (vfld, vx); vy])
		 | App (Const Eq, [TypedForm (App (vfld, vx), _); vy]) (* when equal vx x && equal vy y *) ->
		     let vfield = 
		       if vfld = Const FieldRead then
			 match vx with
			   | hd :: rest -> hd
			   | _ -> debug_msg("\n not good in rewrite_to_smt_reach3 and FieldRead"); vfld
		       else vfld
		     in
		     let f4 = mk_smt_reach3 vfield par1 par2 par2 
		     in 
		       debug_msg ("rewriting into smt_reach3 format... \n" ^ MlPrintForm.string_of_form f4 ^ "\n" ) ;  
		       debug_msg ("vfld: ..\n" ^ MlPrintForm.string_of_form vfld);
		       let f6 = rewrite_gamma (strip_types f4) 
		       in 	
			 debug_msg ( "\n after gamma... \n" ^  PrintForm.string_of_form f6 ^ "\n"  ) ; 
			 f6
		 | App (Const And, [App (Const Eq, [App (vfld, vx); vy]) ;
				    (App((Const Not),[
					   (App((Const Eq),
						[ v; par3 ]))]))]) ->
		     debug_msg ("found rtrancl with forbiden node... " 
				^ PrintForm.string_of_form sub_f ^ "\n" ) ;
		     let f6 = mk_or([
				      rewrite_gamma (mk_smt_reach3 vfld par1 par2 par3) ;
				      mk_and ([	rewrite_gamma (mk_smt_reach3 vfld par1 par2 par2 ) ;
						mk_not(rewrite_gamma( mk_smt_reach3 vfld par1 par3 par3))
					      ])])
		     in
		       f6
		 | App (Const Or, [App (Const Eq, [App (vfld, vx); vy]) ;
					   (App((Const Eq),
						[ v; par3 ]))]) ->
		     debug_msg ("found rtrancl with ternary predicate... " 
				^ PrintForm.string_of_form sub_f ^ "\n" ) ;
		     let f6 = rewrite_gamma (mk_smt_reach3 vfld par1 par2 par3)
		     in
		       f6
		 | _ -> debug_msg ( "\n could not handle: rtrancl_pt...\n "  
				   ^ PrintForm.string_of_form f3 ^ "\n"
				   ^ MlPrintForm.string_of_form f3 ^ "\n"
				   ^ PrintForm.string_of_form sub_f ^ "\n"
				   ^ MlPrintForm.string_of_form sub_f ^ "\n") ; 
		     f3
	      )
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
	 ]
      in


      (*AXIOMS with triggers *)	
      (* avoiding trigges with contain equalities mk_eq( (App(fld, [t1])), t1) z3 complains  *)

      let ax_transitive1_tr fld = (Binder
				     (Forall,
				      [ ("t1",tp); ("t2",tp); ("t3",tp) ],  
				      App(Var smt_trigger_bool_bool,
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
				     App(Var smt_trigger_bool_bool,
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
				      App(Var smt_trigger_bool_bool,
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
				App(Var smt_trigger_bool_bool,
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
				App(Var smt_trigger_bool,
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
				   App(Var smt_trigger_bool,
				       [ (mk_impl( 
					    mk_smt_reach3 fld t1 t2 t1, 
					    mk_eq(t1, t2) )) ; 
					 mk_smt_reach3 fld t1 t2 t1  ] ))) 
      in
      let ax_cycle_tr fld =  (Binder(
				Forall,
				[ ("t1",tp); ("t2",tp) ], 
				App(Var smt_trigger_bool, 
				    [ (mk_impl( mk_and([ mk_eq( (App(fld, [t1])), t1) ; 
							 mk_smt_reach3 fld t1 t2 t2]),  
						mk_eq(t1, t2)  )) ;   
				      mk_smt_reach3 fld t1 t2 t2 ] ))) 
      in   
      let ax_step_tr fld = (Binder(
			      Forall,
			      [ ("t",tp) ], 
			      (TypedForm(App(Var smt_trigger_obj, 
					     [(mk_smt_reach3 fld t (App(fld, [t])) (App(fld, [t]))) ; 
					      (App(fld, [t])) ]),tp_b))))  
      in
	(* axiom ax_reach_tr is missing f(t_1) as antecedent *)
      let ax_reach_tr fld = (Binder(
			       Forall,
			       [ ("t1",tp); ("t2",tp) ],  
			       App(Var smt_trigger_obj_bool, 
				   [(mk_impl( 
				       mk_smt_reach3 fld t1 t2 t2 , 
				       mk_or([ mk_eq(t1,t2) ; 
					       mk_smt_reach3 fld t1 (App(fld, [t1])) t2]))) ;   
				    (App(fld, [t1])) ; 
				    mk_smt_reach3 fld t1 t2 t2  ] ))) 
      in 
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
	   ax_null fld
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
    let f2 = encode_axioms f1 !fieldNames
    in
    let f3 = smart_abstract_constructs [(Var str_smt_reach3, 1)] f2 
    in
      debug_msg ( "\n after smart_abstract_constructs... \n" 
		  ^ MlPrintForm.string_of_form f3 ^ "\n" 
		  ^ PrintForm.string_of_form f2 ^ "\n" ) ;
      f3
