(** Utility functions on {!Ast}: searching, analysis and decomposing. *)

open Ast
open Form
open FormUtil

let arrayVd = {
  vd_name = arrayStateId;
  vd_type = mk_field_type (mk_array mk_object_type);
  vd_jtype = None; (** arrayState does not have an original Java type. *)
  vd_basetype = None; (** arrayState does not have an array base type. *)
  vd_init = None;
  vd_abstract = false;
  vd_def = None;
  vd_field = true;
  vd_ghost = true;
  vd_owner = None;
  vd_class = None;
  vd_encap = (false, false);
}

let empty_prog = { p_types       = [];
                   p_impls       = [];
                   p_specs       = [];
                   p_maps        = [];
                   p_globals     = [];
                   p_ref_fields  = [];
                   p_prim_fields = [] }


(** {6 Creation of programm commands} *)


(** [mkbasic_pp pp bc] makes a command from the program point [pp] and the
    basic command [bc]. *)
let mkbasic_pp (pp : program_point) (c : basic_command) : command =
  Basic {
    bcell_cmd = c;
    bcell_point = pp;
    bcell_known_before = [];
    bcell_known_after = [];
  }

(** An empty programm point. *)
let dummy_program_point : program_point = {
  pp_file = "";
  pp_line = 0;
  pp_class = "";
  pp_proc = "";
  pp_id = 0;
}

(** A counter for program points. *)
let pp_counter : int ref = ref 0

(** Give a fresh program point. *)
let fresh_program_point () =
  pp_counter := !pp_counter + 1;
  { dummy_program_point with pp_id = !pp_counter}

(** Create a command from a basic command. *)
let mkbasic (c : basic_command) : command = 
  mkbasic_pp (fresh_program_point ()) c

(** [smk_cmd_seq cs] makes sequence of commands from the command list [cs]
    while flattening inner seq commands. *)
let smk_cmd_seq (cs : command list) : command =
  let rec mk (cs : command list) : command list =
    match cs with
      | (Seq cs2)::cs1 -> mk (cs2 @ cs1)
      | c::cs1 -> 
	  (match c with 
	     | Basic{bcell_cmd=Assume {annot_form=f}}  (* chop queue after  *)
		 when (f = mk_false) -> [c]            (* an 'assume false' *)
	     | _ -> c::mk cs1)
      | [] -> []
  in
    Seq (mk cs)

(** [mk_assert f msg] creates a command containing an assert of formula [f]
    with comment [msg]. *)
let mk_assert f msg = mkbasic (Assert {
				 hannot_form = f;
				 hannot_about = None;
				 hannot_msg = msg;
				 hannot_hints = [];
				 hannot_forSuch = [];
			       })

(** [patch_hints] adds the formula label to the list of hints. This
    preserves necessary assumptions from the lhs of implications when
    they are lifted from the goal into the assumptions. For unlabelled
    formulas with hints, a fresh label is created. *)
let patch_hints (nf : Specs.noted_form) : ident * ident list =
  let opt_label = nf.Specs.nf_af.Specs.af_annot in
  let hints = nf.Specs.nf_hints  in
    if hints = [] then (opt_label, hints)
    else 
      let label = if opt_label = "" then
	Util.fresh_name "UnnamedLemma" else opt_label
      in
	(label, (Util.set_add label hints))

(** [mk_aassert nf] behaves like [mk_assert nf.nf_af.af_form
    nf.nf_af.af_annot] and also adds the hint list [nf.nf_hints] for the
    proof. *)
let mk_aassert (nf : Specs.noted_form) : command =
  let label, hints = patch_hints nf in
  mkbasic (Assert {
	     hannot_form = nf.Specs.nf_af.Specs.af_form;
	     hannot_about = None;
	     hannot_msg = label;
	     hannot_hints = hints;
	     hannot_forSuch = [];
	   })

(** [mk_assume f msg] is the same as [mk_assert f msg] for creating an
    {!assume} statement. *)
let mk_assume f msg = mkbasic (Assume {
				 annot_form = f;
				 annot_about = None;
				 annot_msg = msg
			       })

(** [mk_assume_false] is an {!assume false} statement without any comment. *)
let mk_assume_false = mk_assume mk_false ""

(** [mk_assume_about v f msg] is the same as [mk_assume f msg] and adds the
    variable [v] affected. *)
let mk_assume_about v f msg = mkbasic (Assume {
				         annot_form = f;
				         annot_about = Some v;
				         annot_msg = msg
			               })

(** [mk_assign lhs res] creates an assignment command which assigns [res]
    to [lhs] and gives [lhs] the type [TypeUniverse]. *)
let mk_assign lhs res = mkbasic (VarAssign {
				   assign_lhs = lhs;
				   assign_tlhs = (lhs,TypeUniverse);
				   assign_rhs = res
				 })

(** Transform an annoted specification into an annoted form command. *)
let mk_noted_form (nf : Specs.noted_form) : hint_annot_form_command =
  let label, hints = patch_hints nf in
  {
    hannot_form = nf.Specs.nf_af.Specs.af_form;
    hannot_about = None;
    hannot_msg = label;
    hannot_hints = hints;
    hannot_forSuch = nf.Specs.nf_forSuch;
  }

(** Create an [noteThat] command out of an annoted specification. *)
let mk_noteThat (nf : Specs.noted_form) : command =
  mkbasic (NoteThat (mk_noted_form nf))

let mk_instantiate (ic : Specs.instantiate_cmd) : command =
  let af = ic.Specs.instantiate_af in
    mkbasic (Instantiate {instantiate_form = af.Specs.af_form;
			  instantiate_annot = af.Specs.af_annot;
			  instantiate_with = ic.Specs.instantiate_with})

let mk_mp (annot : string) (f : form) : command =
  mkbasic (Mp {mp_form = f; mp_annot = annot})

(** [mk_havoc fs] creates the command [havoc fs] for th form list [fs]
    without constraint. *)
let mk_havoc (fs : form list) : command =
  mkbasic (Havoc {havoc_regions=fs; 
		  havoc_msg = "";
		  havoc_constraint = None;
		  havoc_internal = false})

let mk_ephemeral_havoc 
    (fs : form list) (annot : string) : command =
  mkbasic (Havoc {havoc_regions=fs;
		  havoc_msg = annot;
		  havoc_constraint = None;
		  havoc_internal = true})

(** Return the name of a declared variable. *)
let name_of_vd (vd : var_decl) : ident =
  vd.vd_name

(** Return the name of a procedure declaration. *)
let name_of_pd (pd : proc_def) : ident = pd.p_header.p_name


(** {6 Test function} *)


(** Return true if the given variable is a ghost variable. *)
let is_ghost vd = vd.vd_ghost

(** Returns [true] iff the method is [private]. *)
let pd_is_public p = p.p_header.p_public


(** {6 Scanning functions} *)


(** [c_name base name] merges the strings [base] and [name],
    separating them by a dot. *)
let c_name (base : string) (v : string) = base ^ "." ^ v

(** Return the list of local names for the method, ie its arguments and
    local variables. *)
let get_locals (p : proc_def) : ident list =
  List.map (fun vd -> vd.vd_name) (p.p_header.p_formals @ p.p_locals)

(** Return all ghost variables in the program. *)
let get_ghostvars prog =
  let vds = List.flatten (List.map (fun sm -> sm.sm_spec_vars) prog.p_specs) in
  let ids = List.map name_of_vd (List.filter is_ghost vds) in
  let is_assignable id =
    (not (id = arrayStateId)) && (not (id = all_alloc_objs)) in
    List.filter is_assignable ids

(** [find_im name prog] tries to fins the implementation module of name
    [name] into the program [prog]. *)
let find_im (imn : string) (p : program) : impl_module option =
  let rec search = function
    | [] -> None
    | im::ims1 -> if im.im_name = imn then Some im else search ims1
  in search p.p_impls

(** Same as [find_im] but fails if no module is found. *)
let must_find_im imn p =
  match find_im imn p with
    | None -> Util.fail ("Could not find impl module " ^ imn)
    | Some im -> im

(** Same as [find_im] for a specification module. *)
let find_sm (smn : string) (p : program) : spec_module option =
  let rec search = function
    | [] -> None
    | sm::sms1 -> if sm.sm_name = smn then Some sm else search sms1
  in search p.p_specs

(** Same as [must_find_im] for a specification module except that it tries
    to return an object if it finds one before failure. *)
let must_find_sm smn p =
  match find_sm smn p with
    | None ->
        (Util.warn ("Could not find spec module " ^ smn ^ " returning Object");
         match (find_sm "object" p) with
	   | None -> Util.fail ("Util.must_find_sm no 'Object', we are doomed")
	   | Some sm1 -> sm1)
    | Some sm -> sm

(** [find_proc pn im] tries to find a procedure of name [pn] in the
    implementation module [im]. *)
let find_proc (pn : string) (im : impl_module) : proc_def option =
  let rec search = function
    | [] -> None
    | p::ps1 -> if p.p_header.p_name = pn then Some p else search ps1 
  in search im.im_procs

(** Same as [find_proc] but fails if no procedure is found. *)
let must_find_proc pn im =
  match find_proc pn im with
    | None -> Util.fail ("Could not find procedure \"" ^ pn ^ "\" in \
                          implementation module \"" ^ im.im_name ^ "\".")
    | Some im -> im

(** [find_lemma l im] tries to fins a lemma of name [l] in the
    implementation module [im]. *)
let find_lemma (ln : string) (im : impl_module) : form option =
  let rec search = function 
    | [] -> None
    | (ln0,f)::ls1 -> if ln0 = ln then Some f else search ls1
  in search im.im_lemmas

(** Same as [find_proc] for a specification module. *)
let find_proc_header (pn : string) (sm : spec_module) : proc_header option =
  let rec search = function
    | [] -> None
    | ph::phs1 -> if ph.p_name = pn then Some ph else search phs1 
  in search sm.sm_proc_specs

(** [find_var name decl_list] tries to find a variable declaration whose
    name is [name] in the declaration list [decl_list]. *)
let rec find_var (vname : string) (vds : var_decl list) : var_decl option =
  match vds with
    | [] -> None
    | vd::vds1 -> 
	if vd.vd_name = vname then Some vd
	else find_var vname vds1

let impl_modules_claimed_by
    (im : impl_module)
    (prog : program) : impl_module list =
  let imn = im.im_name in
  let rec collect 
      (ims : impl_module list) 
      (acc : impl_module list) : impl_module list =
    match ims with
      | [] -> acc
      | im0::ims1 ->
	  (match im0.im_owner with
	     | Some mn when mn=imn  -> 
		 collect ims1 (im0::acc)
	     | _ -> collect ims1 acc)
  in
    collect prog.p_impls []

(** [find_invariants prog mod free] returns the list of invariants of the
    implementation module whose name is [mod] in the program [prog]. Fails
    if such a module does not exists. If [free] is [true], it includes the
    non-free invariants. *)
let find_invariants (prog : program) (mn : string) (include_free : bool) : Specs.invariant_desc list =
  let im = must_find_im mn prog in
  let get_public_inv (sm1 : spec_module) = 
    (if include_free then sm1.sm_free_invs else []) @ 
      sm1.sm_invs in
  let owned_ims = impl_modules_claimed_by im prog in
  let owned_sms = List.map (fun x -> must_find_sm x.im_name prog) owned_ims in
  let owned_private_invs = 
    List.flatten (List.map (fun x -> x.im_invs) owned_ims)
  in
  let owned_free_invs = List.flatten (List.map (fun x -> x.sm_invs) owned_sms)
  in
  let other_invs = List.concat (List.map get_public_inv prog.p_specs) in
  let invs = im.im_invs @ other_invs @ owned_private_invs @ owned_free_invs in
    List.map Specs.add_comment invs

(** [find_invariant prog mod name] finds the invariant named [name] in the
    implementation module whose mane is [mod] of the program [prog]. It looks
    into non-free invariants. Fails if the program does not constains a
    implementation module named [mod]. *)
let find_invariant (prog : program) (mn : string) (invariant_name : ident) : form =
  let all_invs = find_invariants prog mn true in
  let rec find (invs : Specs.invariant_desc list) = match invs with
    | [] -> 
	(Util.warn ("find_invariant: Could not find invariant " ^ 
		      invariant_name ^ ".\n");
	 mk_var ("UnknownInvariant" ^ invariant_name))
    | {Specs.inv_name=invn; inv_form=f}::invs1 ->
	if invn=invariant_name || (invn=mn ^ "." ^ invariant_name) then f
	else find invs1
  in
    find all_invs

(** {6 Other utility functions} *)

(* 
(** [map_formula impl spec def form] applies abstraction function to
    variables in a formula. -- NOT USED *)
let map_formula
    (impl_vars : ident list)
    (spec_vars : ident list)
    (m : specvar_def list)
    (f : form) : form =
  let rec apply_map 
      (is_old : bool) 
      (m : (ident * form) list) 
      (v : ident) 
      (f : form) : form = 
    match m with
      | [] -> Debug.msg("The abstract variable " ^ v ^ 
			  " is not defined in given refinement.\n"); f
      | (v1,f1)::m1 ->
	  if v1=v then
	    let sub = if is_old then 
	      [(oldname v, oldify true (fv f1) f1)]
	    else [(v1,f1)] 
	    in
	      subst sub f
	  else apply_map is_old m1 v f in
  let rec check_var (v : ident) (f : form) : form =
    let is_old = is_oldname v in
    let uv = if is_old then unoldname v else v in
      if List.mem uv impl_vars then f
      else if List.mem uv spec_vars then
        apply_map is_old m uv f
      else (Debug.msg("Could not map unknown variable " ^ v ^ ".\n"); f) in
  let fvs = fv f in
    List.fold_right check_var fvs f
 *)

(** Declare a variable for the result of the function given as argument. *)
let mk_result_vd (ph : proc_header) : var_decl = {
  vd_name = result_var;
  vd_type = ph.p_restype;
  vd_jtype = ph.p_jtype;
  vd_basetype = ph.p_basetype;
  vd_init = None;
  vd_abstract = false;
  vd_def = None;
  vd_field = false;
  vd_ghost = true;
  vd_owner = None;
  vd_class = None;
  vd_encap = (false, false);
}

(** [specvars_except name prog] returns the list of specification variables
    from all modules of program [prog] except [name]. *)
let specvars_except (smname : string) (prog : program) : var_decl list =
  let get_vars (sm : spec_module) = 
    if sm.sm_name=smname then [] else sm.sm_spec_vars in
    List.concat (List.map get_vars prog.p_specs)

(** Convert a specvar into a variable definition. *)
let vd_of_specvar 
    (is_field : bool)
    (is_abstract : bool) ((id,f) : specvar_def) : var_decl = {
  vd_name = id;
  vd_type = TypeUniverse;
  vd_jtype = None; (* specification variables never have Java types. *)
  vd_basetype = None; (* specification variables do not have array basetypes. *)
  vd_init = None;
  vd_abstract = is_abstract;
  vd_def = None; (* real value is determined later *)
  vd_field = is_field;
  vd_ghost = false;
  vd_owner = None; (* should not be used *)
  vd_class = None;
  vd_encap = (false, false);
}


(** Gets specvars accessible to a given module in the program.
    Those include:
    - specvars of the module
    - specvars directly claimed by it
    - *** specvars of modules with same owner as his one
    - specvars of modules not claimed by any module *)
let accessible_specvars (p : program) (mn : string) : var_decl list =
  let get_specvars (sm : spec_module) = 
    let res() = (List.map (vd_of_specvar false true) sm.sm_constdefs) 
                 @ sm.sm_spec_vars in
      match find_im sm.sm_name p with
	| None -> res()
	| Some im ->
	    (match im.im_owner with
	       | None -> res()
	       | Some mn1 when mn1=mn -> res()
	       | _ -> [])
  in
    List.concat (List.map get_specvars p.p_specs)

(** [deps_lookup var defs] tries to find the free variables of the values
    of the variables [var] into the definition list [defs]. *)
let deps_lookup 
    (vd : var_decl)
    (vdefs : specvar_def list) : ident list option =
  try Some (fv (List.assoc vd.vd_name vdefs))
  with Not_found -> None

(** Compute the set of variable names on which a given variable
    directly (non-transitively) depends, from the viewpoint of given
    module. *)
let support_of 
    (p : program)
    (mname : string)
    (varid : ident) : ident list =
  let check_abst (vd : var_decl) (im : impl_module) : ident list =
    let rec check (maps : mapping list) (acc : ident list) : ident list =
      match maps with
	| [] -> acc
	| map::maps1 ->
	    if map.map_impl = im then
	      (match deps_lookup vd map.map_abst with
		 | Some ids -> check maps1 (List.rev_append ids acc)
		 | None -> check maps1 acc)
	    else check maps1 acc
    in
      check p.p_maps []
  in
    match Util.split_by "." varid with
      | [m;v] ->
	  if m=mname then
	    (* it can be implementation or specification variable *)
	  let sm = must_find_sm mname p in
	  let im = must_find_im mname p in    
	    match find_var varid im.im_vars with
	      | Some vd -> 
		  (match deps_lookup vd im.im_vardefs with
		     | Some ids -> ids
		     | None -> [])
	      | None ->
		  (match find_var varid sm.sm_spec_vars with
		     | Some vd ->
			 (match deps_lookup vd sm.sm_vardefs with
			    | Some ids -> ids
			    | None -> check_abst vd im)
		     | None -> [])
	else
	  (* because it is outside mname,
	     varid is required to be public variable *)
	  let sm = must_find_sm m p in
	    (match find_var varid sm.sm_spec_vars with
	       | Some vd -> 
		   (match deps_lookup vd sm.sm_vardefs with
		     | Some ids -> ids
		     | None -> [])
	       | None -> [])
    | _ -> []

(** Reflextive transitive closure of support_of. *)
let rtrancl_support_of 
    (p : program)
    (mname : string)
    (varid : ident) : ident list =
  let rec closures (ids : ident list) =
    List.concat (List.map closure1 ids)
  and closure1 (id : ident) : ident list =
    match closure id with
      | [] -> [id]
      | ids -> ids
  and closure (id : ident) : ident list =
    closures (support_of p mname id) 
  in
    closure1 varid

(** Dependency relation *)
type def_deps = (ident * ident list) list

(** Return a printable form of the dependence list. *)
let string_of_defdeps (deps : def_deps) : string =
  let pr (v,ids) = v ^ "<-" ^ String.concat ", " ids in
    "[" ^ String.concat "; " (List.map pr deps) ^ "]"

(** Apply [rtrancl_support_of] on all identifires of the list and filter
    the result with the presence of a dot. *)
let rtrancl_support_of_all
    (p : program)
    (mname : string)
    (varids : ident list) : def_deps =
  let is_dotted id  =
    match Util.split_by "." id with
      | [m;v] -> true
      | _ -> false
  in
  let mk_dep (v : ident) =
    (v, List.filter is_dotted (rtrancl_support_of p mname v)) in
    List.map mk_dep varids

(** Inverse of support.  Takes precomputed dependency relation as argument. *)
let affected_by
    (deps : def_deps)
    (id : ident) : ident list =
  let rec collect 
      (deps : def_deps) 
      (acc : ident list) : ident list =
    match deps with
      | [] -> acc
      | (v,dependants)::deps1 -> 
	  if List.mem id dependants then 
	    collect deps1 (v::acc)
	  else
	    collect deps1 acc
  in
    Util.remove_dups (collect deps [])

(** Version of affected_by that accumulates dependencies of a list of
    variables. *)
let affected_by_ids
    (deps : def_deps)
    (ids : ident list) : ident list =
  Util.remove_dups 
    (List.concat (ids::(List.map (affected_by deps) ids)))

(** [var_is_declared_in_spec_module var mod porg] checks if the variable
    [var] is declared in the specification module with name [mod]. Fails if
    such a module does not exist in program [prog]. *)
let var_is_declared_in_spec_module 
    (varid : ident) (smn : ident) (prog : program) : bool =
  let sm = must_find_sm smn prog in
    (match find_var varid sm.sm_spec_vars with
       | Some vd -> true
       | None -> false)

(** [is_rep_var var impl prog] checks whether the variable [var] is a
    representation variable for implementation module [impl] in the program
    [prog]. *)
let is_rep_var
    (varid : ident)
    (im : impl_module)
    (prog : program) : bool =
  let imn = im.im_name in
    match Util.split_by "." varid with
      | [m;v] ->
	  if m=imn then
	    (* it should be implementation variable *)
	  (match find_var varid im.im_vars with
	     | Some vd -> not (var_is_declared_in_spec_module varid imn prog)
		 (* should correspond to (vd.vd_owner = Some im.im_name) *)
	     | None -> false)
	else
	  (* because it is outside mname,
	     varid is required to be public variable *)
	  let sm = must_find_sm m prog in
	  let im1 = must_find_im m prog in
	    (match find_var varid sm.sm_spec_vars with
	       | Some vd -> 
		   (vd.vd_owner = Some imn) ||
                     (im1.im_owner = Some imn)
	       | None -> false)
	
    | _ -> false


(** [pub_mod_vars_claimed_by claim_mod mod def_mod] gets all variables in
    module [def_mod] that are directly claimed by module [claim_mod]. *)
let pub_mod_vars_claimed_by
    (im : impl_module) (* module that claims *)
    (sm : spec_module) (* module where we take variables from *)
    : var_decl list =
  let is_claimed (vd : var_decl) : bool =
    match vd.vd_owner with
      | Some mn when mn=im.im_name -> true
      | _ -> false
  in
    List.filter is_claimed sm.sm_spec_vars

(** Get all variables in a program that are directly claimed by a module *)
let pub_prog_vars_claimed_by
    (im : impl_module)
    (prog : program) : var_decl list =
  List.concat (List.map (pub_mod_vars_claimed_by im) prog.p_specs)

(** [modules_claimed_by mod prog] gets specification modules of modules
    claimed by module [mod] in program [prog]. *)
let modules_claimed_by
    (im : impl_module)
    (prog : program) : spec_module list =
  let imn = im.im_name in
  let rec collect 
      (ims : impl_module list) 
      (acc : spec_module list) : spec_module list =
    match ims with
      | [] -> acc
      | im0::ims1 ->
	  (match im0.im_owner with
	     | Some mn when mn=imn  -> 
		 collect ims1 (must_find_sm im0.im_name prog::acc)
	     | _ -> collect ims1 acc)
  in
    collect prog.p_impls []

(** Get variables that are not claimed from the list of
    variables of a given specification module *)
let get_unclaimed_vars
    (sm : spec_module) : var_decl list =
  let unclaimed (vd : var_decl) = 
    match vd.vd_owner with
      | None -> true
      | _ -> false
  in
    List.filter unclaimed sm.sm_spec_vars

(** Concise display of variable declaration list *)
let pr_vds (vds : var_decl list) : string =
  let get_name vd = vd.vd_name in
    String.concat ", " (List.map get_name vds)


(** Return a list of declarations of representation
    variables for a module in program, consisting of:

  - private variables of im
  - public variables of modules claimed by im that 
    are not claimed as variables by any module
  - public variables claimed by im
 *)
let get_rep_vars
    (im : impl_module)
    (prog : program) : var_decl list =
  im.im_vars @ pub_prog_vars_claimed_by im prog @ 
    List.concat (List.map get_unclaimed_vars (modules_claimed_by im prog))

(** Give the type of a variable *)
let global_var_type (id : ident) (prog : program) : typeForm =
  match Util.split_by "." id with
    | [mname;var] -> 
	let sm = must_find_sm mname prog in
	  (match find_var var sm.sm_spec_vars with
	    | None -> 
		(Util.warn ("astUtil.global_var_type: Could not find " 
				 ^ var ^ " in " ^ mname ^ ", returning unit");
		 mk_unit_type)
	    | Some vd -> vd.vd_type)
    | _ -> 
	(Util.warn ("astUtil.global_var_type: '" ^ id ^ 
		      " is not a qualified variable, returning unit");
	 mk_unit_type)

(** Try to give the type of a concrete variable found among the
    implementation module or procedure header *)
let find_concrete_var_type 
    (prog : program)
    (im : impl_module)
    (pd : proc_def) 
    (id : ident) : typeForm option =
  (** if first string in result is "obj", the second is class name *)
  match (find_var id (pd.p_locals @ pd.p_header.p_formals @ im.im_vars)) with
    | None -> None
    | Some vd -> Some vd.vd_type

(** Get the source of a reference or primitive CONCRETE field *)
let field_source (field : ident) (prog : program) : ident =
  let rec find (fds : field_def list) : ident =
    match fds with
      | [] -> (Util.warn ("astUtil.field_source: could not find field " ^ field);
	       "unknownField")
      | fd::fds1 ->
	  if fd.field_name = field then fd.field_from
	  else find fds1
  in
    find (prog.p_ref_fields @ prog.p_prim_fields)

(** Return a formula giving the owner of the object *)
let mk_owner_of (obj : form) : form =
  mk_fieldRead owner_field obj

(** Return a formula giving the old owner of the object *)
let mk_old_owner_of (obj : form) : form =
  mk_fieldRead old_owner_field obj


(** [mk_class_token_name name] appends [name] to [token_name] *)
let mk_class_token_name (cln : string) : ident =
  token_name ^ "." ^ cln

(** Create a variable from a class name *)
let mk_class_token (cln : string) : form =
  mk_var (mk_class_token_name cln)


(** Create a 'non owner' variable *)
let no_owner_token = mk_class_token no_owner_name

(** Return [true] if the variable is a field *)
let is_field (id : string) (p : program) : bool =
  match Util.split_by "." id with
    | [mname;var] -> 
	(match find_sm mname p with
	   | Some sm -> 
	       (match find_var id sm.sm_spec_vars with
		  | Some vd -> vd.vd_field
		  | None -> 
		      (match find_im mname p with
			 | Some im -> 
			     (match find_var id im.im_vars with
				| Some vd -> vd.vd_field
				| None -> false)
			 | None -> false))
	   | None -> false)
    | _ -> false

(*

(** variable dependencies for derived variables *)
type var_deps = {
  vdep_dep : (ident * ident list) list; 
  (** for each var, list of vars it ultimately depends on;
      the domain and range are disjoint;
      if associated list is empty, the var is a constant *)
  vdep_affects : (ident * ident list) list;
  (** inverse of vdep_dep: for each var, which variables depend on it *)
}


(** Compute all (abstract) variables which depend on a given set of
    variables *)

let support
    (id : ident) 
    (vds : (ident * form) list) : ident list =
  try fv (List.assoc id vds)
  with Not_found -> []

let trans_support
    (id : ident)
    (vds : (ident * form) list) : ident list =

let trans_affected_by
    (ids : ident list)
    (vds : (ident * form) list) : ident list =
*)

(** Create a basic command containing the hint to track the argument
    variable *)
let mk_track_specvar (id : ident) =
  Hint (TrackSpecvar {track_var=id})

(** Get the class names of a program *)
let get_class_names (prog : program) : ident list =
  let get_class_name (sm : spec_module) : ident = sm.sm_name 
  in
    List.map get_class_name prog.p_specs

(** Return the list of variables that are modified or used but not
    allocated in the command. If the command is the entire procedure, then
    for any variable x in the list, x = old(x) at the beginning of the
    procedure. *)
let get_variables_to_old (c : command) : ident list =
  let rec get_variables_to_old_rec
      (c : command) (ids : ident list) : ident list =
    (* ids may contain duplicates *)
    match c with
      | Basic {bcell_cmd = bc} ->
	  begin
	    match bc with
	      | VarAssign {assign_lhs = id} -> id :: ids
	      | Alloc {alloc_lhs = id}
	      | ArrayAlloc {arr_alloc_lhs = id} ->
		  List.filter (fun (x) -> (not (x = id))) ids
	      | ProcCall {callee_res = ido} ->
		  begin
		    match ido with
		      | None -> ids
		      | Some id -> id :: ids
		  end
	      | _ -> ids
	  end
      | Seq cl -> (List.fold_right get_variables_to_old_rec cl ids)
      | Choice cl -> 
	  List.flatten 
            (List.map (fun (x) -> (get_variables_to_old_rec x ids)) cl)
      | If {if_then = it; if_else = ie} ->
	  let it_ids = get_variables_to_old_rec it ids in
	  let ie_ids = get_variables_to_old_rec ie ids in
	    (it_ids @ ie_ids)
      | Loop {loop_prebody = pre; loop_postbody = post} ->
	  let post_ids = get_variables_to_old_rec post ids in
	    get_variables_to_old_rec pre post_ids
      | _ -> ids in
    Util.remove_dups (get_variables_to_old_rec c [])


(** Return the list of all variables in the argument command. *)
let get_all_variables_by_type (c : command) : typedIdent list =
  let rec get_all_variables_rec
      (tids : typedIdent list) (c : command) : typedIdent list =
    let not_declared (id : ident) : bool =
      not (List.exists (fun (id0, tf) -> id = id0) tids) in
    let check_declared (ids : ident list) : unit =
      let not_declared_ids = List.filter not_declared ids in
	if (not (not_declared_ids = [])) then
	  begin
	    print_string "WARNING: The following variables are not declared.\n";
	    List.iter (fun (id) -> print_string (id ^ " ")) not_declared_ids;
	    print_string ("\n")
	  end; in
    (* ids may contain duplicates *)
      match c with
	| Basic {bcell_cmd = bc} ->
	    begin
	      match bc with
		| VarAssign {assign_tlhs = tid; assign_rhs = f} ->
		    check_declared (FormUtil.fv f);
		    tids @ [tid]
		| Alloc {alloc_tlhs = tid} -> 
		    tids @ [tid]
		| ArrayAlloc {arr_alloc_tlhs = tid; arr_alloc_dims = fs} ->
		    let f_ids = List.flatten (List.map FormUtil.fv fs) in
		      check_declared f_ids;
		      tids @ [tid]
		| ProcCall {callee_res = ido; callee_args = fs;
                            callee_hdr = hdro} ->
		    let f_ids = List.flatten (List.map FormUtil.fv fs) in
		      check_declared f_ids;
		      begin
			match ido with
			  | None -> tids
			  | Some id -> 
			      match hdro with
				| None ->
				    print_string 
                                      "WARNING: Missing callee header.\n"; tids
				| Some hdr ->
				    (id, hdr.p_restype) :: tids
		      end
		| _ -> tids
	    end
        | Assuming _ -> Util.fail "get_all_variables_rec: \
                                  uncaught pattern matching case 'Assuming'.\n"
        | PickAny _ -> Util.fail "get_all_variables_rec: \
                                  uncaught pattern matching case 'PickAny'.\n"
        | PickWitness _ -> Util.fail "get_all_variables_rec: \
                                  uncaught pattern matching case 'PickWitness'.\n"
        | Induct _ -> Util.fail "get_all_variables_rec: \
                                 uncaught pattern matching case 'Induct'.\n"
	| Contradict _ -> Util.fail "get_all_variables_rec: \
                                 uncaught pattern matching case 'Contradict'.\n"
	| Proof _ -> Util.fail "get_all_variables_rec: \
                                uncaught pattern matching case 'Proof'.\n"
	| Seq cl -> (List.fold_left get_all_variables_rec tids cl)
	| Choice cl -> 
	    List.flatten
              (List.map (fun (x) -> (get_all_variables_rec tids x)) cl)
	| If {if_condition = ic; if_then = it; if_else = ie} ->
	    check_declared (FormUtil.fv ic);
	    let it_tids = get_all_variables_rec tids it in
	    let ie_tids = get_all_variables_rec tids ie in
	      (it_tids @ ie_tids)
	| Loop {loop_prebody = pre; loop_test = test; loop_postbody = post} ->
	    check_declared (FormUtil.fv test);
	    let pre_tids = get_all_variables_rec tids pre in
	      get_all_variables_rec pre_tids post
	| Return {return_exp = re} ->
	    match re with
	      | None -> tids
	      | Some f -> check_declared (FormUtil.fv f); tids in
    Util.remove_dups (get_all_variables_rec [] c)

(** Strip asserts that should be ignored by the unsound command-line option. *)
let strip_ignored_asserts (c : command) : command =
  let rec one_contained_in (sl : string list) (msg : string) : bool =
    match sl with
      | [] -> false
      | s::sl1 -> 
	  if Util.substring s msg then true
	  else one_contained_in sl1 msg 
  in
  let rec strip c =
    match c with
      | Basic({bcell_cmd=bc} as ce) -> Basic{ce with bcell_cmd=strip_bc bc}
      | Seq cs -> Seq (List.map strip cs)
      | Choice cs -> Choice (List.map strip cs)
      | Loop ({loop_prebody=c1; loop_postbody=c2} as lc) -> 
	  Loop{lc with loop_prebody=strip c1; loop_postbody=strip c2}
      | If ({if_then=c1; if_else=c2} as ic) -> 
	  If{ic with if_then=strip c1; if_else=strip c2}
      | Return _ -> c
      | PickAny({pa_body=cs} as pa) ->
	  PickAny{pa with pa_body=List.map strip cs}
      | PickWitness({pw_body=cs} as pw) ->
	  PickWitness{pw with pw_body=List.map strip cs}
      | Assuming({assuming_body=cs} as a) ->
	  Assuming{a with assuming_body=List.map strip cs}
      | Induct({induct_body=cs} as ic) ->
	  Induct{ic with induct_body=List.map strip cs}
      | Contradict({contradict_body=cs} as cc) ->
	  Contradict{cc with contradict_body=List.map strip cs}
      | Proof({proof_body=cs} as pc) ->
	  Proof{pc with proof_body=List.map strip cs}

  and strip_bc (bc : basic_command) : basic_command =
    match bc with
      | Assert{hannot_msg=m} when 
	  (one_contained_in (!CmdLine.ignore_asserts) m) ||
	  (!CmdLine.prove_only_asserts <> [] && 
           not (one_contained_in (!CmdLine.prove_only_asserts) m))
	-> Skip
      
      | _ -> bc
  in strip c

(** Return the callee header of the procedure call. Fail if it does not
    exists. *)
let get_callee_hdr (pc : proc_call) : proc_header =
  match pc.callee_hdr with
    | None -> failwith ("astUtil: unresolved call to " ^ pc.callee_name)
    | Some h -> h

(** Given the fully-qualified name of a field, [vd_of_field] tries to find
    the corresponding variable declaration, if any. *)
let vd_of_field (prog : program) (fld : ident) : var_decl option =
  match Util.split_by "." fld with
    | [mname;fname] ->
	(let imo = find_im mname prog in
	 let fld_vdo0 = match imo with
	   | Some im0 -> find_var fld im0.im_vars
	   | None -> None in
	   match fld_vdo0 with
	     | Some vd -> Some vd
	     | None ->
		 let smo = find_sm mname prog in
		   match smo with
		     | Some sm0 ->
			 find_var fld sm0.sm_spec_vars
		     | None -> None)
    | _ -> None

(** Get the names of the variables affected by a 'havoc' statement. *)
let get_havoc_vars havoc = 
  List.map
    (function
       | TypedForm (Var x, _)
       | Var x -> x
       | other -> invalid_arg "AstUtil.get_havoc_vars")
    havoc.havoc_regions

(** Return the modified variables by a command. *)
let get_modified_vars cmd =
  let rec modified_vars acc = function
    | Basic {bcell_cmd = VarAssign assign} ->
        if assign.assign_lhs = arrayStateId
        then
          begin  (* array affectation *)
            match assign.assign_rhs with
              | TypedForm (App (Const ArrayWrite,
                                [a; TypedForm (Var arr, _); index; v]), _)
              | TypedForm (App (Const ArrayWrite, [a; Var arr; index; v]), _)
              | App (Const ArrayWrite, [a; TypedForm (Var arr, _); index; v])
              | App (Const ArrayWrite, [a; Var arr; index; v]) -> arr :: acc
              | rhs -> Util.fail ("get_modified_vars: ill-formed array assignm\
                                 ent '" ^ PrintForm.string_of_form rhs ^ "'.\n")
          end (* variable affectation *)
        else assign.assign_lhs :: acc
    | Basic {bcell_cmd = Alloc ac} -> ac.alloc_lhs :: acc
    | Basic {bcell_cmd = ArrayAlloc aac} -> aac.arr_alloc_lhs :: acc
    | Basic {bcell_cmd = Havoc h} -> 
        (List.map unvar (List.filter is_var h.havoc_regions)) @ acc
    | Basic {bcell_cmd = ProcCall pc} ->
        List.map unvar
          (List.filter is_var
             (Util.unsome (Util.unsome pc.callee_hdr).p_contract.co_mod))
        @ acc
    | Seq command_list
    | Choice command_list ->
        List.fold_left modified_vars acc command_list
    | If {if_then = first; if_else = second}
    | Loop {loop_prebody = first; loop_postbody = second} ->
        modified_vars (modified_vars acc first) second
    | PickAny {pa_vars = vars_list}
    | PickWitness {pw_vars = vars_list} -> (List.map fst vars_list) @ acc
    | _ -> acc
  in
    modified_vars [] cmd
