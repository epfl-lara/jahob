(** Transform Ast to normal form by making all assertions
    explicit and desugaring loops and procedure calls *)

open Ast
open AstUtil
open Form
open FormUtil
open Background

(* Debug messages *)
let debug_id = Debug.register_debug_module "Sast"
let debug_lmsg = Debug.debug_lmsg debug_id
let debug_is_on =  fun () -> Debug.debug_is_on debug_id

(* ------------------------------------------------------------ *)
(** Modifies clause handling *)
(* ------------------------------------------------------------ *)


(* extract variable from a formula representing havoc region *)
let rec region_to_id rf = match rf with
  | TypedForm(rf1, t) -> region_to_id rf1
  | Var v -> [v]
  | _ -> Util.warn (
      "sast.region_to_id: havoc of complex regions not supported, but got '" ^
	PrintForm.short_string_of_form rf ^ "'\n"); []

(** Compute a set of global variables that give *upper* approximation 
    of the modifies region given by the formula, e.g. 
    x..f is approximated by f *)
let rec mod_upper_bound (f : form) : ident list =
  match (strip_types f) with
    | Var id -> [id]
    | App(Const FieldRead, [Var field;obj]) -> [field]
    | App(Const ArrayRead, _) -> [arrayStateId]
    | TypedForm(f1,t) -> mod_upper_bound f1
    | _ -> (Util.warn ("Sast.mod_upper_bound: could not recognize mod item " ^ 
			 PrintForm.string_of_form f);
	    [])

(** Compute a set of global variables that give *lower* approximation 
    of the modifies region given by the formula, 
    e.g. the list [x..f; y] is approximated by y 
    because not all of f is allowed to be modified. *)
let mod_lower_bound (fs0 : form list) : ident list =
  let rec collect (fs : form list) (acc : ident list) : ident list =
    match fs with
      | [] -> acc
      | f::fs1 ->
	  (match f with
	     | Var id -> collect fs1 (id::acc)
	     | TypedForm(fmain,_) -> collect (fmain::fs1) acc
	     | _ -> 
		 debug_lmsg 0 (fun () ->"Threw away mod clause item " ^
			      PrintForm.string_of_form f ^ "\n");
		 collect fs1 acc)
  in
    collect fs0 []

(** split_mod separates modifies clause containing x..f into a list of modified variables f and
    frame condition for x..f 

If \q{f} is a field such that no item of the form \q{f} appears
in modifies clause, but an item of the form \q{e..f} appears
in the modifies clause, then let $\q{e}_1\q{..f}$,
\ldots, $\q{e}_n\q{..f}$ be all such expressions.  As just described,
then \q{f} is removed from the list of variables with full
frame conditions, but a partial frame condition is introduced of
the form:

ALL x::obj. x: old alloc.T & x ~= null &
               x ~= old e1 & ... & x ~= old en &
               old (x..owner) ~= C &
  -->  
    x..f = old (x..f)
*)
type field_mods = (ident * form list) list

let split_mod 
    (prog : program)
    (base_class : string) (** base class of procedure *)
    (encap_opt : bool) (** whether it is safe to apply encapsulation optimization **)
    (fs0 : form list) (** formulas describing modifies clausees *)
    (mention_hidden : bool)  (** whether to assume that hidden objects can be changed *)
    : (ident list (** modified vars *) * form list (** frame condition conjuncts *) )  =

  let ins (ids : ident list) (id : ident) : ident list =
    if List.mem id ids then ids else id::ids in

  let rec mod_ins (field : ident) (obj : form) (fmods : field_mods) =
    match fmods with
      | [] -> [(field,[obj])]
      | (field1,objs1)::fmods1 ->
	  if field1=field then (field1,obj::objs1)::fmods1
	  else (field1,objs1)::mod_ins field obj fmods1 in

  let post_of_fmod ((f, es) : (ident * form list)) : form =
    let new_special_ident = "new" in
    let rec is_new_special_ident = function
      | TypedForm(e1,t) -> is_new_special_ident e1
      | Var id -> id = new_special_ident
      | _ -> false 
    in
      if f = arrayStateId then
	let fvar = mk_var f in
	let xid = "framedArrObj" in
	let xvar = mk_var xid in
	let iid = "i" in
	let ivar = mk_var iid in
	let xtypename = Util.unqualify_getting_module f in
	let hidden_set = mk_var (AstUtil.c_name base_class Jast.hidden_set_name) in
	let elem = smk_and (
	  [mk_lteq(mk_int 0, ivar);
	   mk_lt(ivar, mk_fieldRead arrayLengthVar xvar);
	   mk_elem(xvar,mk_var (oldname (obj_var xtypename)))]
	  @ if mention_hidden then [mk_not (mk_elem(xvar, hidden_set))] else []
	) in
	let mk_diff (e : form) : form = 
	  if is_new_special_ident e then mk_elem(xvar, mk_var (oldname all_alloc_objs))
	  else mk_neq(xvar,make_old_and_transform e [xid])
	in
	let diff = List.map mk_diff es in
	let lhs = smk_and ([elem] @ diff) in
	let rhs = mk_eq(mk_arrayRead fvar xvar ivar,
			mk_arrayRead (mk_var (oldname f)) xvar ivar) in
	let res = mk_forall(xid,mk_object_type,
			    mk_forall(iid,mk_int_type,
				      smk_impl(lhs,rhs))) in
	  if encap_opt then
	    let _ = debug_lmsg 0 
	      (fun () -> "Eliding: " ^ (PrintForm.string_of_form res)) in
	      mk_true
	  else 
	    let _ = debug_lmsg 0 
	      (fun () ->"Array mod post formula: " ^ 
		 (PrintForm.string_of_form res)) in
	      res
      else 
    let fvar = mk_var f in
    let xid = "framedObj" in
    let xvar = mk_var xid in
    let xtypename = Util.unqualify_getting_module f in
    let hidden_set = mk_var (AstUtil.c_name base_class Jast.hidden_set_name) in
    let elem = smk_and (
      [mk_elem(xvar,mk_var (oldname all_alloc_objs)); mk_elem(xvar,mk_var (obj_var xtypename))] 
      @	(if mention_hidden
         then [mk_not (mk_elem(xvar, hidden_set))] else [])
    )     
    in
    let mk_diff (e : form) : form = 
      if is_new_special_ident e then mk_true
      else mk_neq(xvar,make_old_and_transform e [xid])
    in
    let diff = List.map mk_diff es in
    let lhs = smk_and ([elem] @ diff) in
    let rhs = mk_eq(mk_fieldRead fvar xvar,
		    mk_fieldRead (mk_var (oldname f)) xvar) in
    let res = mk_forall(xid,mk_object_type, smk_impl(lhs,rhs)) in
      (** Encapsulation optimization applies when:
	  - the method for which this postcondition is being 
	    computed is encapsulated (encap_opt is true)
	  - the field is encapsulated
	  - the method and field belong to the same class
	  - the receiver object is not one of the objects for 
	    which this formula is required to hold
      **)
    let field_vd = vd_of_field prog f in
    let encap_field = 
      match field_vd with
	| Some vd -> let is_encap, _ = vd.vd_encap in is_encap
	| None -> false in
    let same_class = (xtypename = base_class) in
    let this_in_diff = List.mem (Var this_id) es in
      if encap_opt && encap_field && same_class && this_in_diff then
	let _ = debug_lmsg 0 (fun () -> "Eliding: " ^ (PrintForm.string_of_form res)) in
	  mk_true
      else
	let _ = debug_lmsg 0 (fun () -> "Field mod post formula: " ^ PrintForm.string_of_form res) in
	  res
  in

  let collect_mods (fs : form list) =
    let collect_vars (fs : form list) : ident list =
      let fs_ids = List.map unvar fs in
	List.fold_left ins [] fs_ids
    in
    let check_fields (ids : ident list) (fs : form list) : form list =
      let rec checkr (hd : form list) (tl : form list) : form list =
	match tl with
	  | [] -> hd
	  | f::fs0 ->
	      match f with
		| App(Const FieldRead, [Var field; f0]) -> 
		    if (List.mem field ids) then
		      (print_string 
			 ("\nWarning: " ^ (PrintForm.string_of_form f) ^ 
			    " in modifies clause is redundant with " ^ 
			    field ^ " in modifies clause. " ^
			    "This is probably an error. Ignoring...\n");
		       checkr hd fs0)
		    else
		      checkr (hd @ [f]) fs0
		| _ -> checkr (hd @ [f]) fs0
      in	    
	checkr [] fs
    in
    let rec collect (fs : form list) (ids : ident list) (fmods : field_mods) =
    match fs with
      | [] -> (ids,fmods)
      | f::fs1 -> 
	  (match f with
	     | App(Const FieldRead, [Var field;obj]) ->
		 (debug_lmsg 0 (fun () ->"Modifies reading " ^ field ^ "\n");
		 collect fs1 (ins ids field) (mod_ins field obj fmods))

	     | App(Const ObjLocs, [f]) ->
		 (Util.warn ("Objlocs not supported yet, item " ^ 
				  PrintForm.string_of_form f);
		  collect fs1 ids fmods)
	     | _ -> (Util.warn ("Unsupported modifies clause item " ^ 
				  PrintForm.string_of_form f);
		     collect fs1 ids fmods)) in
    let fs_vars, fs_rest = List.partition is_var fs in
    let ids = collect_vars fs_vars in
    let fs_checked = check_fields ids fs_rest in
      collect fs_checked ids []
  in
(* actual split_mod body*)
  let (vars,fmods) = collect_mods (List.map strip_types fs0) in
  let _ = debug_lmsg 0 (fun () ->"Fields in split_mod: " ^ 
			  String.concat ", " (List.map fst fmods)) in
    (vars, List.map post_of_fmod fmods)



(** Compute an upper bound on the set of variables
    modified by the execution of a command. *)
let modified_vars_of (c0 : command) : ident list =
  let ids = ref ([] : ident list) in
  let add_id (id : string) : unit =
    if List.mem id !ids then () 
    else ids := id::!ids in
  let form_collect (f : form) : unit =
    List.iter add_id (mod_upper_bound f) in
  let havoc_collect (fs : form list) : unit = 
    List.iter form_collect fs in
  let b_collect (b : basic_command) : unit = match b with
    | Skip -> ()
    | VarAssign {assign_lhs=id} -> add_id id 
    | Alloc {alloc_lhs=id} -> add_id id
    | ArrayAlloc _ -> () (** no 'add_id arrayStateId', 
			     array alloc does not change array content *)
    | Assert _ -> ()
    | NoteThat _ -> ()
    | Assume _ -> ()
    | Split _ -> ()
    | Havoc {havoc_regions=fs} -> havoc_collect fs
    | ProcCall {callee_hdr=Some {p_contract={co_mod=Some fs}}} -> 
	havoc_collect fs
    | ProcCall {callee_module=m;callee_name=p} ->
	debug_lmsg 0 (fun () ->"Could not find modifies clause for " ^ m ^ "." ^ p)
    | Hint _ -> ()
    | Instantiate _ -> ()
    | Mp _ -> ()
 in
  let rec collect (c : command) : unit = match c with
    | Basic {bcell_cmd=b} -> b_collect b
    | Seq cs -> List.iter collect cs
    | Choice cs -> List.iter collect cs
    | If {if_then=c1;if_else=c2} -> collect c1; collect c2
    | Loop {loop_prebody=c1;loop_postbody=c2} -> collect c1; collect c2
    | Return _ -> ()
    | PickAny {pa_body=cs}
    | PickWitness {pw_body=cs}
    | Assuming {assuming_body=cs}
    | Induct {induct_body=cs}
    | Contradict {contradict_body=cs} 
    | Proof {proof_body=cs} -> List.iter collect cs
  in
    collect c0;
    !ids

(* ------------------------------------------------------------ *)
(** END of modifies clauses *)
(* ------------------------------------------------------------ *)

(** Conjoin formula with public and private invariants,
    and concretize abstract variables. *)
let conjoin_concretize 
    (prog : program) 
    (im : impl_module)
    (is_public : bool)
    (f : form) = 
  let smname = im.im_name in
  let sm = must_find_sm smname prog in  
  let get_public_inv (sm1 : spec_module) = 
    ListLabels.map ~f:(Specs.good_looking_inv ~msg:("WhileIn_" ^ smname ^ "_OutsidePublicInvOf_" ^ sm1.sm_name)) sm1.sm_invs 
  in
  let get_private_invs (label : string) (im1 : impl_module) : form list = 
    if is_public then 
      ListLabels.map ~f:(Specs.good_looking_inv ~msg:(im1.im_name ^ label)) im1.im_invs 
    else [] 
  in
  let get_our_free_invs (label : string) (sm1 : spec_module) : form list =
    ListLabels.map ~f:(Specs.good_looking_inv ~msg:(sm1.sm_name ^ label)) sm1.sm_free_invs 
  in
  let private_invariants = get_private_invs "_PrivateInv" im in
  let our_free_invariants = get_our_free_invs "_FreeInv" sm in
  let owned_ims = impl_modules_claimed_by im prog in
  let owned_sms = List.map (fun x -> must_find_sm x.im_name prog) owned_ims in
  let owned_private_invs = 
    List.flatten (List.map (get_private_invs "_OwnedPrivateInv") owned_ims)
  in
  let owned_free_invs = 
    List.flatten (List.map (get_our_free_invs "_OwnedFreeInv") owned_sms)
  in
  let relevant_invariants =
    private_invariants @
      our_free_invariants @
      owned_private_invs @
      owned_free_invs @
      List.concat (List.map get_public_inv prog.p_specs)
  in
    (mk_and (f :: relevant_invariants))

(** precondition of a procedure *)
let concretized_pre 
    (prog : program) 
    (im : impl_module)
    (ph : proc_header) = 
  conjoin_concretize prog im ph.p_public ph.p_contract.co_pre

(** postcondition of a procedure *)
let concretized_post
    (prog : program) 
    (im : impl_module)
    (p : proc_def)
    (ph : proc_header) 
    (desugared_body : command)
    = 
  let hidden_set_name = AstUtil.c_name im.im_name Jast.hidden_set_name in

  (** preservation of values for variables that seem syntactically
      modified but are not declared such.  Because client will not
      havoc those at all, we must ensure that they are equal everywhere.
      If you havoc them only nowhere else other than 
      on newly allocated objects, you must still mention them,
      You can use 'new' as a dummy, so you can write 
         new..arrayState
      or new..fieldName 
  *)
  let mk_post_obligation 
      (prog : program) 
      (base_class : string)
      (ignore_hidden : bool)
      (encap_opt : bool) (** whether the relevant method is encapsulated **)
      (f : ident) : form = 
    let tag id frm = mk_comment (id ^ "_preserved_") frm in
    let hidden_set = mk_var hidden_set_name in
      (if f = arrayStateId then
      let fvar = mk_var f in
      let xid = "framedArrObj" in
      let xvar = mk_var xid in
      let iid = "i" in
      let ivar = mk_var iid in
      let xtypename = Util.unqualify_getting_module f in
      let elem = smk_and (
	[mk_lteq(mk_int 0, ivar);
	 mk_lt(ivar, mk_fieldRead arrayLengthVar xvar);
	 mk_elem(xvar,mk_var (oldname (obj_var xtypename)))]
	@ if ignore_hidden then [mk_not (mk_elem(xvar, hidden_set))] else []
      ) in
      let lhs = elem in
      let rhs = mk_eq(mk_arrayRead fvar xvar ivar,
		      mk_arrayRead (mk_var (oldname f)) xvar ivar) in
      let res = mk_forall(xid,mk_object_type,
		  mk_forall(iid,mk_int_type,
			    smk_impl(lhs,rhs))) in
      let _ = debug_lmsg 0 (fun () ->"Field mod post formula: " ^ PrintForm.string_of_form res) in
	tag f res      
    else if AstUtil.is_field f prog then
      let fvar = mk_var f in
      let xid = "framedObj" in
      let xvar = mk_var xid in
      let xtypename = Util.unqualify_getting_module f in
      let elem = [mk_elem(xvar,mk_var (oldname (obj_var xtypename)))]
	@ (if ignore_hidden then [mk_not (mk_elem(xvar, hidden_set))] else [])
      in
      let lhs = smk_and elem in
      let rhs = mk_eq(mk_fieldRead fvar xvar,
		      mk_fieldRead (mk_var (oldname f)) xvar) in
      let res = mk_forall(xid,mk_object_type,
			  smk_impl(lhs,rhs)) in
      let _ = debug_lmsg 0 (fun () ->"Field mod post formula: " ^ PrintForm.string_of_form res) in
	tag f res
    else
      tag f (mk_eq(mk_var f,mk_var (oldname f)))
      )
  in

  let names_of_locals = List.map AstUtil.name_of_vd p.p_locals in
  let procedure_mod = ph.p_contract.co_mod in
  let check_modifies () : form list =
    (** remove local variables from a list *)
    let non_locals_of (ids : ident list) : ident list =
      let not_local id = not (List.mem id names_of_locals) in
	List.filter not_local ids
    in
    let modified_vars = 
      non_locals_of (modified_vars_of desugared_body) in
    let _ = Debug.lmsg 4 (fun () ->"Modified variables in body of " ^ 
			im.im_name ^ "." ^ ph.p_name ^ ":\n  " ^
			String.concat ", " modified_vars ^ "\n") in      
    let avars = accessible_specvars prog im.im_name in
    let avar_names = List.map AstUtil.name_of_vd avars in
      (* !! Change to use defined_affected_by? *)
    let deps = rtrancl_support_of_all prog im.im_name avar_names in
    let _ = debug_lmsg 0 (fun () ->"Dependencies:\n" ^ string_of_defdeps deps ^"\n") in
    let ultimately_modified = affected_by_ids deps modified_vars in
    let _ = debug_lmsg 0 (fun () ->"Ultimately modified variables in body of " ^ 
			im.im_name ^ "." ^ ph.p_name ^ ":\n  " ^
			String.concat ", " ultimately_modified ^ "\n") in
    let not_private (id : ident) : bool = not (is_rep_var id im prog) in
    let visible_modified = 
      if ph.p_public then List.filter not_private ultimately_modified 
      else ultimately_modified
    in
    let (declared1,field_post_mod) = match procedure_mod with
      | None -> ([],[])
      | Some fs -> split_mod prog im.im_name ph.p_encap fs (!CmdLine.checkHidden) in
    let declared = result_var :: hidden_set_name :: all_alloc_objs :: declared1 in
    let _ = debug_lmsg 0 (fun () ->"Mod clause is: " ^
			String.concat ", " declared ^ "\n") in
    let is_undeclared id = not (List.mem id declared) in
    let undeclared_modified = List.filter is_undeclared visible_modified in
    let _ = 
      if undeclared_modified = [] then
	Util.msg ("No undeclared modified vars.")
      else 
	Util.msg ("Syntactically modified variables: [" ^
		     String.concat ", " undeclared_modified ^ "]" ^
		     " are not declared in the body of " ^ 
		     im.im_name ^ "." ^ ph.p_name ^ ". " ^
       "Jahob will try to prove their objects are new or semantically same.\n") 
    in
      field_post_mod @ 
	List.map (mk_post_obligation prog im.im_name ph.p_public ph.p_encap) undeclared_modified
  in
  let post_mod = mk_comment "FrameCondition" (smk_and (check_modifies())) in
  conjoin_concretize prog im ph.p_public (smk_and [ph.p_contract.co_post; post_mod])

(** diagnostic *)
let pr_map (m : (ident * form) list) : unit =
  let pr_sub (f1,f2) = 
    print_string (f1 ^ " --> " ^ 
		      PrintForm.string_of_form f2 ^ " ") in
  let _ = Debug.msg "Substitution:\n  " in
    List.iter pr_sub m; print_string "\n"

let desugar_only_init : bool ref = ref false
let desugar_only_init_set () : unit = desugar_only_init := true
let desugar_only_init_uns () : unit = desugar_only_init := false

let init_suffix = "_init"

(** Desugaring procedure calls *)
let desugar_procedure_call
    (prog : program)
    (im : impl_module) (* caller module *)
    (pc : proc_call) (* procedure call and callee info *) 
    : command list * (ident * ident) list =
  (* Procedure call (but see code for details):

     z := p(v)

     where p(u) has:
       requires pre(x,y,u)
       modifies x
       ensures post(old(x),x,y,u,result)

     becomes:
       assert pre(x,y,v);
       x0 := x;
       havoc x;
       havoc privateRep (if reentrant)
       havoc z;
       assume post(x0,x,y,v,z)

     Improvement needed for dependent variables: 
       do not save modified x, but 
        those variables that are referred to as 'old' in post.
        this can be smaller than x if some are not referred to,
        and can be bigger if there are dependent variables.
  *)
  let hdr = get_callee_hdr pc in
  let callee_sm = must_find_sm pc.callee_module prog in
  let full_callee_name = callee_sm.sm_name ^ "." ^ hdr.p_name in
  let spec = hdr.p_contract in

  let add_callee_invs f = smk_and (f:: (ListLabels.map ~f:Specs.good_looking_inv callee_sm.sm_invs)) in
  let c_pre = add_callee_invs spec.co_pre in
  let c_post1 = add_callee_invs spec.co_post in
  let modspec = match spec.co_mod with
    | None -> (** interpreting no modifies clause as an empty modifies clause *)
	[]
    | Some s -> s in

    (** handling call backs *)
  let callback_possible = hdr.p_public && im.im_name = callee_sm.sm_name in

  let (mods0,field_post) = split_mod prog callee_sm.sm_name false modspec (!CmdLine.checkHidden && callback_possible) in
  let alloc_monotone = mk_subseteq(mk_var (oldname all_alloc_objs), 
				   mk_var all_alloc_objs) in
  let c_post = smk_and (c_post1::alloc_monotone::field_post) in

  let rep_mods = 
    if callback_possible then
      arrayStateId :: List.map (fun vd -> vd.vd_name) (get_rep_vars im prog)
    else []
  in

    (** modifies clause at granularity of variables *)
  let mods = all_alloc_objs :: rep_mods @ mods0 in
  let add_external f = 
    if pc.call_is_external then conjoin_concretize prog im hdr.p_public f
    else f in

  (* u -> v: 
     replacing formal parameters with actual arguments
     used both in pre and post *)

  let formals = List.map (fun x -> x.vd_name) hdr.p_formals in
  let m_u_v1 = 
    try List.combine formals pc.callee_args
    with Invalid_argument s ->
      failwith (s ^ ": Argument mismatch calling " ^ full_callee_name) in
  let old_formals = List.map (fun x -> oldname x.vd_name) hdr.p_formals in
  let m_u_v2 = 
    try List.combine old_formals pc.callee_args
    with Invalid_argument s ->
      failwith (s ^ ": Argument mismatch calling " ^ full_callee_name) in
  let map_u_v = m_u_v1 @ m_u_v2 in

  (* assert precondition *)

  let assert_pre = [mk_assert (add_external (subst map_u_v c_pre))
    (full_callee_name ^ "_Precondition")] in

  (* find variables refered to with 'old' in the postcondition *)
  let old_from_post = List.map unoldname (List.filter is_oldname (fv c_post)) in
  let old_from_post = 
    List.filter (fun x -> not (List.mem x formals)) old_from_post in

  (* establish mapping (x0,x) of modified variables *) 
  let mk_map_x_x0 = 
    if !desugar_only_init 
    then (desugar_only_init_uns (); fun x -> (x, x ^ init_suffix))
    else fun x -> (x, Util.fresh_name x) in
  let map_x_x0 = List.map mk_map_x_x0 old_from_post in

  (* x0 := x
     save values of modified variables *)

  let map_to_assign (x,x0) = mk_assign x0 (mk_var x) in
  let assigns_to_save_state = List.map map_to_assign map_x_x0 in

  (* havoc x *)

  let havoc_x = [mk_havoc (List.map mk_var mods)] in

  (* havoc z *)

  let havoc_z = 
    match pc.callee_res with
      | None -> []
      | Some z -> [mk_havoc [mk_var z]] in

    (* TODO: replace renamings with assignments? *)

  (* old x -> x0  renaming *)

  let mk_map_oldx_x0 x = 
    try (oldname x, mk_var (List.assoc x map_x_x0))
    with Not_found -> Util.fail "Internal error desugaring procedure call"
  in
  let m_oldx_x0 = List.map mk_map_oldx_x0 old_from_post in
  (* let _ = pr_map m_oldx_x0 in *)

  (* result -> z: result parameter in the post *)

  let map_result_z = 
    match pc.callee_res with
      | None -> []
      | Some z -> [(result_var,mk_var z)] in

  (* assume postcondition *)
    
  let mapped_c_post = subst (map_u_v @ m_oldx_x0 @ map_result_z) c_post in

  let old_remained = List.filter is_oldname (fv mapped_c_post) in
  let _ = if old_remained <> [] then
    Util.warn ("Error disambiguating old references [" ^ 
		 String.concat ", " old_remained ^ "]") else ()
  in

  let assume_post = [mk_assume 
    (add_external mapped_c_post)
    (full_callee_name ^ "_Postcondition")] in

  (* final desugaring result for desugar_procedure_call: *)
  assert_pre 
  @ assigns_to_save_state
  @ havoc_x
  @ havoc_z
  @ assume_post,
  map_x_x0

let desugar_alloc (prog : program) (x : ident) (t : ident) : command list =
  (* x = new t
     --->
     havoc x;
     assume x ~= null & x ~: alloc_t & x : t & lonely x;
     alloc := alloc Un {x}
  *)
  let xf = mk_var x in
  let x_type = mk_elem(xf,mk_var (obj_var t)) in
  let x_nin_alloc = mk_notelem(xf,all_alloc_objsf) in
  let x_nonnull = mk_neq(xf,mk_null) in
  let alloc_assumption = 
    smk_and [x_nonnull; x_nin_alloc; x_type;
	     get_unalloc_lonely_xid prog x]
  in
    [mk_havoc [mk_var x];
     mk_assume alloc_assumption "AllocatedObject";
     mk_assign all_alloc_objs 
       (mk_cup(all_alloc_objsf, mk_singleton xf))]
      
let desugar_array_alloc 
    (prog : program)
    (x : ident) 
    (t : ident) 
    (ds : form list) : command list =
  (* x = new T[d1];
     --->
     havoc x;
     assume x ~= null & x ~: alloc_t & x : Array & x..length=d1 & lonely x &
     (ALL i. 0 <= i & i < d1 --> x.[i] = null);
     alloc := alloc Un {x}
  *)
  match ds with
    | [] -> Util.warn "vcgen.wp_array_alloc: array with no dimensions"; []
    | d1::ds1 ->
	let _ = (if ds1 <> [] then 
		   Util.warn "vcgen.wp_array_alloc: multidim array"
		 else ()) in
	let xf = mk_var x in
	let x_nonnull = mk_neq(xf,mk_null) in
	let x_nin_alloc = mk_notelem(xf,all_alloc_objsf) in
	let x_length = mk_eq(mk_arrayLength xf,d1) in
	let x_has_array_type = mk_elem(xf,mk_var Jast.array_std_class_name) in
	let iid = "nli" in
	let iidf = mk_var iid in
	let one_elem = mk_arrayRead1 xf iidf in
	let elements_null =
	  mk_forall(iid,mk_int_type,
		    mk_impl(mk_and [mk_lteq(mk_int 0,iidf); 
				    mk_lt(iidf,d1)],
			    mk_eq(one_elem, mk_null))) in
	let alloc_assumption = 
	  smk_and [x_nonnull; x_nin_alloc; x_has_array_type; 
		   x_length;
		   get_unalloc_lonely_xid prog x;
		   elements_null]
	in
	  [mk_havoc [mk_var x];
	   mk_assume alloc_assumption "AllocatedArrayObject";
	   mk_assign all_alloc_objs 
	     (mk_cup(all_alloc_objsf, mk_singleton xf))]

let desugar_instantiate (ic : instantiate_command) : command list =
  (** "instantiate ALL x. f with y" desugars into:
      
      assert ALL x. f(x);
      assume f(y);
  *)
  let rec instantiate (f : form) (fs : form list) : form =
    match f, fs with
      | (Binder(Forall, (id, _)::ids, f'), x::xs) ->
	  let f' = smk_foralls (ids, f') in
	  let f' = subst [(id, x)] f' in
	    instantiate f' xs
      | (App(Const Comment, [msg; f']), _) ->
	  App(Const Comment, [msg; instantiate f' fs])
      | (TypedForm(f', ty), _) -> 
	  mk_typedform (instantiate f' fs, ty)
      | (_, []) -> f
      | _ -> Util.warn ("Not enough quantified variables in:\n" ^
			  (PrintAst.pr_basic_cmd (Instantiate ic)) ^ "\n"); f
  in
  let f = ic.instantiate_form in
  let fs = ic.instantiate_with in
  let annot = ic.instantiate_annot
  in
    [mk_assert f annot;
     mk_assume (instantiate f fs) annot]

let desugar_mp (mc : mp_command) : command list =
  let rec split (f : form) : form * form = 
    match f with
      | App(Const Impl, [p; q]) -> (p, q)
      | App(Const Comment, [_; f'])
      | TypedForm(f', _) -> split f'
      | _ -> Util.warn 
	  ("Arguments to 'mp' must have form 'p --> q':\n" ^
	     (PrintAst.pr_basic_cmd (Mp mc)) ^ "\n"); (mk_true, f)
  in
  let f = mc.mp_form in
  let p, q = split f in
  let annot = mc.mp_annot
  in
    [mk_assert f annot; 
     mk_assert p annot; 
     mk_assume q annot]
      
let desugar_basic 
    (prog : program) 
    (im : impl_module) 
    (add_new_local : ((ident * ident) -> unit))
    (bc : basic_command) : command list = 
  let _ = debug_lmsg 0 
    (fun () -> "desugar_basic: " ^ (PrintAst.pr_basic_cmd bc)) in
  let same = [mkbasic bc] in
    match bc with
      | Skip -> []
      | VarAssign va -> same
      | Alloc{alloc_lhs=x;alloc_type=t} -> desugar_alloc prog x t
      | ArrayAlloc{arr_alloc_lhs=lhs;arr_alloc_type=t;arr_alloc_dims=ds} ->
	  desugar_array_alloc prog lhs t ds
      | Assert _ -> same
      | NoteThat nt -> 
	  if !CmdLine.proofstmts then
	  [mkbasic (Assert nt);
	   mk_assume nt.hannot_form nt.hannot_msg]
	  else []
      | Assume _ -> same
      | Split _ -> same
      | Havoc ({havoc_regions=rs;
		havoc_msg=msg;
		havoc_constraint=fo;
		havoc_internal=internal} as hc) -> 
	  (match fo with
	       | None -> same
	       | Some f ->
		   let bindings = 
		     List.map (fun v -> (v,TypeUniverse))
		       (List.concat (List.map region_to_id rs)) in
		     [mkbasic (Havoc {hc with havoc_constraint = None});
		      mk_assert (mk_existses(bindings,f)) 
			("HavocFeasible" ^ if msg="" then "" else "_"^msg);
		      mk_assume f msg])
      | ProcCall pc -> 
	  let pc', new_locals = desugar_procedure_call prog im pc in
	    List.iter add_new_local new_locals;
	    pc'
      | Hint _ -> same
      | Instantiate ic ->
	  if !CmdLine.proofstmts then
	    desugar_instantiate ic
	  else [mkbasic Skip]
      | Mp mc ->
	  if !CmdLine.proofstmts then
	    desugar_mp  mc
	  else [mkbasic Skip]

let mk_post_assert (prog : program) (im : impl_module) (pd : proc_def) (desugared_body : command) : form =
  let res = concretized_post prog im pd pd.p_header desugared_body in
  let _ = Util.msg("Post assert for " ^ pd.p_header.p_name ^ " is:\n" ^ PrintForm.string_of_form res ^ "\n") in
    res

let rec ensure_proof_command (c : command) : unit =
  let not_proof c = Util.fail ("Not a proof command:  \n" ^ 
				 PrintAst.pr_basic_cmd c) in
  let check_basic (bc : basic_command) : unit =
    match bc with
      | Skip 
      | Assert _
      | NoteThat _
      | Assume _
      | Split _
      | Hint _ 
      | Instantiate _
      | Mp _ -> ()
      | Havoc {havoc_internal=ok} when ok -> ()
      | c -> not_proof c
  in
  let rec check (c : command) : unit =
    match c with
      | Basic{bcell_cmd=bc} -> check_basic bc
      | Seq cs -> List.iter check cs
      | Choice cs -> List.iter check cs
      | Loop lc -> Util.fail "Encountered loop construct in proof block"
      | If{if_then=thenc;if_else=elsec} -> (check thenc; check elsec)
      | Return _ -> Util.fail "Encountered 'return' in proof block"
      | PickAny{pa_body=cs}
      | PickWitness{pw_body=cs}
      | Assuming{assuming_body=cs}
      | Induct{induct_body=cs}
      | Contradict{contradict_body=cs}
      | Proof{proof_body=cs} -> List.iter check cs
  in check c

let to_patch_comment = "TOPATCH" 
let patched_comment = "ProcedureEndPostcondition"
let trivial_post_assert() = mk_assert (mk_var "toBePatched") to_patch_comment

let patch_asserts (asf : form) (c : command) : unit =
  let no_patched = ref 0 in
  let rec patch (c : command) : unit =
    match c with
      | Basic{bcell_cmd=bc} -> 
	  (match bc with
	   | Skip -> ()
	   | VarAssign va -> ()
	   | Alloc _ -> Util.warn("Alloc not desugared.")
	   | ArrayAlloc _ -> Util.warn ("Array alloc not desugared.")
	   | Assert ({hannot_msg=m} as a) ->
	       if m=to_patch_comment then
		 (a.hannot_form <- asf;
		  a.hannot_msg <- patched_comment;
		  incr no_patched)
	       else Util.msg("Did not patch assert called " ^ m ^"\n")
	   | NoteThat _ -> Util.warn ("noteThat not desugared.")
	   | Assume _ -> ()
	   | Split _ -> ()
	   | Havoc _ -> ()
	   | ProcCall pc -> Util.warn ("Procedure call not desugared.")
	   | Hint _ -> ()
	   | Instantiate _ -> Util.warn ("instantiate command not desugared.")
	   | Mp _ -> Util.warn ("mp command not desugared."))
    | Seq cs -> List.iter patch cs
    | Choice cs -> List.iter patch cs
    | Loop lc -> Debug.msg ("Note: loop was not desugared.\n")
    | If _ -> Util.warn ("If command not desugared")
    | Return _ -> Util.warn ("Return command not desugared")
    | PickAny _ -> Util.warn ("pickAny command not desugared")
    | PickWitness _ -> Util.warn ("pickWitness command not desugared")
    | Assuming _ -> Util.warn ("'assuming' command not desugared")
    | Induct _ -> Util.warn ("induct command not desugared")
    | Contradict _ -> Util.warn ("contradict command not desugared")
    | Proof _ -> Util.warn ("proof command not desugared")
in 
  let res = patch c in
  let _ = Util.msg (Printf.sprintf "Patched %d asserts with formula\n %s \n" !no_patched 
		   (PrintForm.string_of_form asf)) in
    res

let desugar_return 
    (prog : program) 
    (im : impl_module) 
    (pd : proc_def) 
    (oexp : form option)
    : command = 
  let return_end = mk_assume mk_false "ProcedureReturn" in
  let post_assert = trivial_post_assert() in
    match oexp with
      | None -> smk_cmd_seq [post_assert; return_end]
      | Some exp -> smk_cmd_seq [mk_assign result_var exp;
				 post_assert; return_end]

let desugar_proc_def 
    (prog : program)
    (im : impl_module)
    (pd : proc_def) : unit =

  let add_the_local vd =
    (pd.p_locals <- vd :: pd.p_locals)
  in

  let new_locals = ref [] in
  let add_new_local =
    let var_decls = 
      let jtype = match pd.p_header.p_formals with
	| [] -> None
	| vd :: _ -> vd.vd_jtype in
      let this_decl = 
	{vd_name = this_id;
	 vd_type = mk_object_type;
	 vd_jtype = jtype;
	 vd_basetype = None;
	 vd_init = None;
	 vd_abstract = false;
	 vd_ghost = false;
	 vd_def = None;
	 vd_field = false;
	 vd_owner = None;
	 vd_class = None;
	 vd_encap = (false, false);
	}
      in
      List.fold_left 
	(fun var_decls sm -> sm.sm_spec_vars @ var_decls)  
	(this_decl :: Util.union pd.p_locals im.im_vars) prog.p_specs
    in fun (x, x0) ->
      let x_decl = try
	List.find 
	  (fun v_decl -> v_decl.vd_name = x) 
	  var_decls
      with Not_found ->
	failwith ("desugar_proc_def: cannot find local " ^ x ^ "\n")
      in new_locals := {x_decl with vd_name = x0} :: !new_locals
  in
  let c_pre = concretized_pre prog im pd.p_header in
  let pre_assume = mk_assume c_pre "ProcedurePrecondition" in

  let mk_havoc_alloced (id : ident) : command list = (* used in desugar_loop *)
    match (find_var id (pd.p_locals @ pd.p_header.p_formals @ im.im_vars)) with
      | Some vd -> 
	  (match vd.vd_type with
	     | TypeApp (TypeObject,[]) -> 
		 let type_info = 
		   (match vd.vd_class with
		      | Some cname -> [mk_elem(mk_var id,mk_var cname)]
		      | None -> [])
		 in
		   [mk_assume 
		      (smk_and 
			 (mk_elem(mk_var id,all_alloc_objsf)::type_info))
		      (id ^ "_alloced_loop")]
	     | _ -> [])
      | None -> []
  in
  let rec desugar_loop (lc : loop_command) : command =
    let c1 = desugar lc.loop_prebody in
    let cond = lc.loop_test in
    let c2 = desugar lc.loop_postbody in
    let assume_cond = mk_assume cond "LoopConditionHolds" in
    let assume_ncond = mk_assume (mk_not cond) "LoopConditionFalse" in
    let loop_inv_assert = 
      match lc.loop_inv with
	| None -> []
	| Some inv -> [mk_assert inv "LoopInvariantHoldsDuringUnrolling"] in
    let loop_end = mk_assume mk_false "CodeUnreachableAfterLoop" in
    let rec unroll (k : int) : command =
      if (k <= 0) then loop_end
      else smk_cmd_seq
	([c1] @
	 loop_inv_assert @
	 [Choice [assume_ncond;
		  smk_cmd_seq [assume_cond; c2; unroll (k-1)]]])
    in
      if !CmdLine.bounded_loop_unroll then 
	unroll !CmdLine.unroll_factor
      else 
	match lc.loop_inv with
	  | None -> Loop {lc with
	               loop_prebody = c1;
		       loop_inv = None;
		       loop_test = cond;
		       loop_postbody = c2} (* leaving loop in there *)
	  | Some inv -> (* ESC/Java-like desugaring *)
	      let mod_ids = Util.remove_dups 
		((modified_vars_of c1) @ (modified_vars_of c2)) in
	      let havoced_allocated = List.concat (List.map mk_havoc_alloced mod_ids) in
	      let loop_entry_alloc = Util.fresh_name all_alloc_objs in
	      let _ = add_the_local
		{vd_name = loop_entry_alloc;
		 vd_type = mk_obj_set_type;
		 vd_jtype = None; (** Object.alloc does not have a Java type. *)
		 vd_basetype = None;
		 vd_init = None;
		 vd_abstract = false;
		 vd_ghost = false;
		 vd_def = None;
		 vd_field = false;
		 vd_class = None;
		 vd_owner = None;
		 vd_encap = (false, false);
		} in
	      let alloc_loop_monotone = 
		mk_assume (mk_subseteq ((mk_var loop_entry_alloc),all_alloc_objsf))
		  "alloc_loop_monotone"
	      in
		smk_cmd_seq
		  ([mk_assert inv "LoopInvHoldsInitially";
		    mk_assign loop_entry_alloc all_alloc_objsf;
		    mk_havoc (List.map mk_var mod_ids);
		    alloc_loop_monotone]
		   @ havoced_allocated @ 
		   [mk_assume inv "AssumingLoopInv";
		    c1;
		    Choice [smk_cmd_seq [assume_cond; 
					c2; 
					mk_assert inv "LoopInvPreserved";
					loop_end];
			    assume_ncond]])

  and desugar_pickAny (pa : pickAny_command) : command =
    let _ = List.iter ensure_proof_command pa.pa_body in
    let picked_ids = List.map (fun (v,t)->v) pa.pa_vars in
    let rec collect_forSuch cs acc =
      match cs with
	| [] -> acc
	| Basic{bcell_cmd=
	      NoteThat{
		  hannot_msg=msg;
		  hannot_form=f;
		  hannot_forSuch=ids}}::cs1 when ids = picked_ids ->
	    collect_forSuch cs1 ((f,msg)::acc)
	| _::cs1 -> collect_forSuch cs1 acc in
    let consequences = collect_forSuch pa.pa_body [] in
    let globalize (f : form) = 
      match pa.pa_hyp with
	| None -> smk_foralls(pa.pa_vars,f)
	| Some h -> smk_foralls(pa.pa_vars,smk_impl(h,f))
    in
    let assume_of_conseq ((f,msg) : form * string) : command =
      mk_assume (globalize f) msg in
    let havoc_vars = mk_ephemeral_havoc 
      (List.map (fun (v, _) -> Var v) pa.pa_vars) pa.pa_hypAnnot in
    let assume_feasible = 
      match pa.pa_hyp with
	| None -> [havoc_vars]
	| Some h -> 
	    [havoc_vars;
	     (* This is left over from when we allowed 
		executable code in pickAny. Without this
		check the optional suchThat clause 
		becomes a shorthand for pickAny-assuming.
		
		mk_assert 
	      (smk_exists(pa.pa_vars, h))
	      (pa.pa_hypAnnot^"Feasible"); *)
	     mk_assume h pa.pa_hypAnnot]
    in
    let inside_block = 
      Seq (assume_feasible @ 
	   List.map desugar pa.pa_body @
	   [mk_assume_false])
    in
      Seq (Choice [mkbasic Skip;
		   inside_block]
	   ::List.map assume_of_conseq consequences)

  and desugar_pickWitness (pw : pickWitness_command) : command =
    let _ = List.iter ensure_proof_command pw.pw_body in
    let mk_consequence cs =
      try
	let c = List.nth cs (List.length cs - 1) in
	  match c with
	    | Basic{bcell_cmd=
		  NoteThat{
		    hannot_msg=msg;
		    hannot_form=f;
		    hannot_forSuch=ids}} when ids = [] ->
		[mk_assume f msg]
	    | _ -> []
      with _ -> []
    in
    let consequence = mk_consequence pw.pw_body in
    let havoc_vars = mk_ephemeral_havoc 
      (List.map (fun (v, _) -> Var v) pw.pw_vars) pw.pw_hypAnnot in
    let assume_feasible = 
      match pw.pw_hyp with
	| None -> [havoc_vars]
	| Some h -> 
	    [havoc_vars;
	     mk_assert
	       (smk_exists(pw.pw_vars, h))
	       (pw.pw_hypAnnot^"Feasible");
	     mk_assume h pw.pw_hypAnnot]
    in
    let inside_block = 
      Seq (assume_feasible @ 
	   List.map desugar pw.pw_body @
	   [mk_assume_false])
    in
      Seq (Choice [mkbasic Skip;
		   inside_block]
	   ::consequence)

  and desugar_assuming (a : assuming_command) : command =
    let _ = List.iter ensure_proof_command a.assuming_body in
    let assume_hyp = mk_assume 
      a.assuming_hyp
      (match a.assuming_hypAnnot with Some s -> s | None -> "AssumingHyp")
    in
    let assert_goal = mkbasic (Assert a.assuming_goal) in
    let assume_impl = mk_assume (mk_impl(a.assuming_hyp,
					 a.assuming_goal.hannot_form))
                                a.assuming_goal.hannot_msg
    in
      Seq [Choice [mkbasic Skip;
		   Seq([assume_hyp] @
			 List.map desugar a.assuming_body @
			 [assert_goal;
			  mk_assume_false])];
	   assume_impl]

  and desugar_induct (ic : induct_command) : command =
    (** "induct f(n) over n in c" desugars into:

	(skip [] 
	  (havoc n; 
	   assume 0 <= n;
	   c; 
	   assert f(0); 
	   assert f(n) --> f(n + 1); 
	   assume false));
	assume ALL n. 0 <= n --> f(n)
    *)
    let induct_body = ic.induct_body in
    let _ = List.iter ensure_proof_command induct_body in
    let n, ty = ic.induct_var in
    let f = ic.induct_form in
    let nvar = Var n in
    let zero = mk_int 0 in
    let fb = subst [(n, zero)] f in
    let fi = smk_impl (f, subst [(n, mk_plus (nvar, mk_int 1))] f) in
    let annot = ic.induct_annot in
    let n_hyp = mk_lteq(zero, nvar) in
    let base_assert = mk_assert fb (annot ^ "BaseCase") in
    let induct_assert = mk_assert fi (annot ^ "InductCase") in
    let induct_proof = 
      Seq ([mk_ephemeral_havoc [nvar] annot; mk_assume n_hyp annot] @ 
	     List.map desugar induct_body @ 
	     [base_assert; induct_assert; mk_assume_false]) in
    let fc = smk_forall (n, ty, smk_impl(n_hyp, f)) in
      Seq [Choice [mkbasic Skip; induct_proof]; mk_assume fc annot]

  and desugar_contradict (cc : contradict_command) : command =
    (** "contradict f in c" desugars into:

	(skip [] 
	  (assume ~f;
	   c; 
	   assert false;
	   assume false;));
	assume f;
    *)
    let _ = List.iter ensure_proof_command cc.contradict_body in
    let f = cc.contradict_form in
    let annot = cc.contradict_annot in
    let assume_hyp = mk_assume (smk_not f) annot in
    let assert_goal = mk_assert mk_false annot in
    let assume_impl = mk_assume f annot
    in
      Seq [Choice [mkbasic Skip;
		   Seq([assume_hyp] @
			 List.map desugar cc.contradict_body @
			 [assert_goal;
			  mk_assume_false])];
	   assume_impl]

  and desugar_proof (p : proof_command) : command =
    (** "proof in (c; note f)" desugars into:

	(skip [] 
	 (c; 
	  assert f; 
	  assume false)); 
	assume f;
    *)
    let body = p.proof_body in
    let _ = List.iter ensure_proof_command body in
    let goal = p.proof_goal in
    let assert_goal = mkbasic (Assert goal) in
    let assume_goal = mk_assume goal.hannot_form goal.hannot_msg
    in
      Seq [Choice [mkbasic Skip;
		   Seq(List.map desugar body @
			 [assert_goal;
			  mk_assume_false])];
	   assume_goal]

  and desugar (c : command) : command =
    match c with
      | Basic{bcell_cmd = bc} -> 
	  smk_cmd_seq (desugar_basic prog im add_new_local bc)
      | Seq cs -> smk_cmd_seq (List.map desugar cs)
      | Choice cs -> Choice (List.map desugar cs)
      | If {if_condition=cond; if_then=c1; if_else=c2} ->
	  let c1d = desugar c1 and c2d = desugar c2 in
	    Choice [smk_cmd_seq [mk_assume cond "TrueBranch"; c1d];
		    smk_cmd_seq [mk_assume (mk_not cond) "FalseBranch"; c2d]]
      | Loop lc -> desugar_loop lc
      | Return ret -> desugar_return prog im pd ret.return_exp
      | PickAny pa -> 
	  if !CmdLine.proofstmts then
	    desugar_pickAny pa
	  else mkbasic Skip
      | PickWitness pw -> 
	  if !CmdLine.proofstmts then
	    desugar_pickWitness pw
	  else mkbasic Skip
      | Assuming a -> 
	  if !CmdLine.proofstmts then 
	    desugar_assuming a 
	  else mkbasic Skip
      | Induct ic ->
	  if !CmdLine.proofstmts then
	    desugar_induct ic
	  else mkbasic Skip
      | Contradict cc ->
	  if !CmdLine.proofstmts then
	    desugar_contradict cc
	  else mkbasic Skip
      | Proof pc ->
	  if !CmdLine.proofstmts then
	    desugar_proof pc
	  else mkbasic Skip
  in
  let desugared_body_core = desugar pd.p_body in
    (* This commented code would generate too many useless assignments,
       instead we still remember to replace old with non-old versions in vcgen:

      let mk_old_assignment (id : ident) : command =
      mk_assign (oldname id) (mk_var id) in
      let old_equals_current = 
      List.map mk_old_assignment 
      (modified_vars_of desugared_body_core) in
    *)
    (* be careful below, the order matters due to all side effects *)
  let b1 = smk_cmd_seq [desugared_body_core; trivial_post_assert()] in
  let _ = (pd.p_locals <- pd.p_locals @ !new_locals) in
  let _ = patch_asserts (mk_post_assert prog im pd desugared_body_core) b1 in
  let desugared_body = 
    AstUtil.strip_ignored_asserts
      (smk_cmd_seq [pre_assume; b1])
  in
    pd.p_simple_body <- Some {sb_body = desugared_body};
    pd.p_body <- desugared_body

let desugar_program (p : program) : unit =
  let desugar_impls (im : impl_module) : unit =
    List.iter (desugar_proc_def p im) im.im_procs
  in
    List.iter desugar_impls p.p_impls

let rec desugar_only_loop ?return_name (* used to optionally handle returns *)
    (prog : program) (im : impl_module) (lc : loop_command) : command =
  let c1 = desugar_only ?return_name prog im [] lc.loop_prebody in
  let cond = lc.loop_test in
  let c2 = desugar_only ?return_name prog im [] lc.loop_postbody in
  let assume_cond = mk_assume cond "LoopConditionHolds" in
  let assume_ncond = mk_assume (mk_not cond) "LoopConditionFalse" in
  let loop_inv_assert = 
    match lc.loop_inv with
      | None -> []
      | Some inv -> [mk_assert inv "LoopInvariantHoldsDuringUnrolling"] in
  let loop_end = mk_assume mk_false "CodeUnreachableAfterLoop" in
  let rec unroll (k : int) : command =
    if (k <= 0) then loop_end
    else smk_cmd_seq
      ([c1] @
	 loop_inv_assert @
	 [Choice [assume_ncond;
		  smk_cmd_seq [assume_cond; c2; unroll (k-1)]]])
  in
    if !CmdLine.bounded_loop_unroll then 
      unroll !CmdLine.unroll_factor
    else 
      match lc.loop_inv with
	| None -> Loop {lc with
			  loop_prebody = c1;
			  loop_postbody = c2} (* leaving loop in there *)
	| Some inv -> (* ESC/Java desugaring *)
	    let mod_ids = Util.remove_dups 
	      ((modified_vars_of c1) @ (modified_vars_of c2)) 
	    in
	      smk_cmd_seq
		[mk_assert inv "LoopInvHoldsInitially";
		 mk_havoc (List.map mk_var mod_ids);
		 mk_assume inv "AssumingLoopInv";
		 c1;
		 Choice [smk_cmd_seq [assume_cond; 
				      c2; 
				      mk_assert inv "LoopInvPreserved";
				      loop_end];
			 assume_ncond]]

and desugar_only ?return_name (* used to optionally handle returns *)
    (prog : program) 
    (im : impl_module) 
    (ignore : command list) (* List of commands not to desugar. *)
    (c : command) : command =
  if List.mem c ignore then c
  else
    match c with
      | Basic{bcell_cmd = bc} -> 
	  smk_cmd_seq (desugar_basic prog im (fun x -> ()) bc)
      | Seq cs ->
          smk_cmd_seq (List.map (desugar_only ?return_name prog im ignore) cs)
      | Choice cs ->
          Choice (List.map (desugar_only ?return_name prog im ignore) cs)
      | If {if_condition = cond; if_then = c1; if_else = c2} ->
	  let c1d = desugar_only ?return_name prog im ignore c1 and 
	      c2d = desugar_only ?return_name prog im ignore c2 in
	    Choice [smk_cmd_seq [mk_assume cond "TrueBranch"; c1d];
		    smk_cmd_seq [mk_assume (mk_not cond) "FalseBranch"; c2d]]
      | Loop lc -> desugar_only_loop ?return_name prog im lc
      | Return ret ->
          begin
            match return_name with
              | None ->
                  Util.fail "desugar_only: does not handle 'return' commands"
              | Some name ->
                  begin
                    match ret.return_exp with
                      | None ->
                          mkbasic (VarAssign {assign_lhs = name;
                                              assign_tlhs = (name,mk_unit_type);
                                              assign_rhs = mk_unit})
                      | Some retexp -> 
                          mkbasic (VarAssign {assign_lhs = name;
                                              assign_tlhs = (name,TypeUniverse);
                                              assign_rhs = retexp})
                  end
          end
      | Assuming _
      | PickAny _ 
      | PickWitness _ 
      | Induct _ 
      | Contradict _ 
      | Proof _ -> Util.fail ("desugar_only: uncaught pattern matching " ^
          "cases 'Assuming', 'PickAny', 'PickWitness', 'Induct', and 'Contradict'")

let check_desugared_basic (bc : basic_command) : unit =
  match bc with
    | Skip -> ()
    | VarAssign va -> ()
    | Alloc _ -> Util.warn("Alloc not desugared.")
    | ArrayAlloc _ -> Util.warn ("Array alloc not desugared.")
    | Assert _ -> ()
    | NoteThat _ -> Util.warn ("noteThat not desugared.")
    | Assume _ -> ()
    | Split _ -> ()
    | Havoc _ -> ()
    | ProcCall pc -> Util.warn ("Procedure call not desugared.")
    | Hint _ -> ()
    | Instantiate _ -> Util.warn ("instantiate command not desugared.")
    | Mp _ -> Util.warn ("mp command not desugared.")

let rec check_desugared (c : command) : unit =
  match c with
    | Basic{bcell_cmd=bc} -> check_desugared_basic bc
    | Seq cs -> List.iter check_desugared cs
    | Choice cs -> List.iter check_desugared cs
    | Loop lc -> Debug.msg ("Note: loop was not desugared.\n")
    | If _ -> Util.warn ("If command not desugared")
    | Return _ -> Util.warn ("Return command not desugared")
    | PickAny _ -> Util.warn ("pickAny command not desugared")
    | PickWitness _ -> Util.warn ("pickWitness command not desugared")
    | Assuming _ -> Util.warn ("'assuming' command not desugared")
    | Induct _ -> Util.warn ("'induct' command not desugared")
    | Contradict _ -> Util.warn ("'contradict' command not desugared")
    | Proof _ -> Util.warn ("'proof' command not desugared")

let check_desugared_program (p : program) : unit =
  let check_proc (pd : proc_def) : unit =
    match pd.p_simple_body with
      | Some {sb_body=c} -> check_desugared c
      | None -> Util.warn ("There is no body of method " ^ pd.p_header.p_name ^"\n") in
  let check_impl (im : impl_module) : unit =
    List.iter check_proc im.im_procs
  in
    List.iter check_impl p.p_impls

let ast2sast (p : program) : program =
  desugar_program p;
  check_desugared_program p;
  Util.fail_if_warned("Desugaring of ast failed.");
  p
