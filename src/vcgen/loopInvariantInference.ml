(** Loop invariant inference *)

open Ast
open Form
open FormUtil

(* Debugging for this module. *)
let debug_id : int = Debug.register_debug_module "LoopInvariantInference"
let debug_msg : (string -> unit) = Debug.debug_msg debug_id
let debug_lmsg = Debug.debug_lmsg debug_id
let debug_is_on ?(level=1) =
  fun () -> Debug.debug_is_on debug_id & !Debug.debug_level >= level

(* History of inference for the current loop. *)
type history_t = {
  mutable h_passed : form list;
  mutable h_failed : form list;
  h_loop : loop_command;
}

type inference_env_t = {
  ie_program : program;
  ie_impl : impl_module;
  ie_proc : proc_def;
  ie_phdr : proc_header;
  ie_conc : specvar_def list;
  ie_precondition : form;
  ie_iterations : int;
  ie_classes : ident list;
  ie_fvs : ident list;
  ie_timeout : float;
}

type expr_t = 
  | BoundExpr of form * typedIdent list
  | FreeExpr of form

type equiv_class_t = expr_t list
type equiv_classes_t = equiv_class_t list

type context_t =
  | SetElement of form
  | Field of form
  | Arg of int * form

type context_map_t = (context_t, expr_t list) Hashtbl.t

exception InferenceFailure of string

(* Formula manipulations, etc. *)

let rec not_constant (f : form) : bool =
  match f with
    | Const _ -> false
    | TypedForm(f0, _)
    | App(Const Comment, [_; f0]) -> not_constant f0
    | _ -> true

let make_eq_to_old (id : ident) : form =
  mk_eq ((Var id), (Var (FormUtil.oldname id)))

let get_callee_header (pc : proc_call) : proc_header =
  match pc.callee_hdr with
    | Some header -> header
    | None -> 
	let msg = "get_callee_header: not found for " ^ pc.callee_name in
	  raise (InferenceFailure msg)

(* Find equalities in the formula, and return the list of ident's for
   use with smk_fixand_eq. *)
let rec get_candidates_for_substitution 
    (ids : ident list) (f : form) : ident list =
  match f with
    | Var _ 
    | Const _ -> ids
    | App(Const Eq, [Var v; _])
    | App(Const Eq, [_; Var v]) -> 
	if (not (List.mem v ids)) then
	  v :: ids
	else
	  ids
    | App(f0, fs) ->
	let ids0 = get_candidates_for_substitution ids f0 in
	  List.fold_left get_candidates_for_substitution ids0 fs
    | Binder(_, _, f0)
    | TypedForm(f0, _) ->
	get_candidates_for_substitution ids f0

(* Compute the maximum loop depth by recursive descent. *)
let rec get_loop_depth (c : command) : int =
  match c with
    | Seq cl
    | Choice cl ->
	let get_max_depth (d : int) (c0 : command) : int =
	  let d0 = get_loop_depth c0 in
	    if (d0 > d) then d0 else d
	in
	  (List.fold_left get_max_depth 0 cl)
    | If {if_then = it; if_else = ie} ->
	let it_d = get_loop_depth it in
	let ie_d = get_loop_depth ie in
	  if (it_d > ie_d) then it_d else ie_d
    | Loop lc ->
	let pre_d = get_loop_depth lc.loop_prebody in
	let post_d = get_loop_depth lc.loop_postbody in
	  if (pre_d > post_d) then (pre_d + 1) else (post_d + 1)
    | _ -> 0

type modvars_cache_t = (loop_command, ident list) Hashtbl.t

(* Since the modified variables of a loop are also the modified
   variables of the outer loops, we want to have a cache. *)
let get_modified_variables (c : command) (cache : modvars_cache_t) : ident list =
  let rec get_modified_variables_rec (ids : ident list) (c : command) : ident list =
    match c with
      | Basic {bcell_cmd = bc} ->
	  (match bc with
	     | VarAssign {assign_lhs = id} -> 
		 Util.set_add id ids
	     | ProcCall {callee_res = reso} ->
		 (match reso with
		    | None -> ids
		    | Some res -> Util.set_add res ids)
	     | _ -> ids)
      | Seq cl
      | Choice cl ->
	  (List.fold_left get_modified_variables_rec ids cl)
      | If {if_then = it; if_else = ie} ->
	  let it_mv = (get_modified_variables_rec ids it) in
	    (get_modified_variables_rec it_mv ie)
      | Loop lc ->
	  (try Hashtbl.find cache lc with Not_found ->
	     let post_mv = (get_modified_variables_rec ids lc.loop_postbody) in
	       (Hashtbl.add cache lc post_mv); post_mv)
      | _ -> ids in
    get_modified_variables_rec [] c

(* Gather together all the formulas in a given command. *)
let rec find_forms_in_command = function
  | Basic {bcell_cmd = bc} ->
      begin
	match bc with
	  | VarAssign ac -> [ac.assign_rhs]
	  | ArrayAlloc aac -> aac.arr_alloc_dims
	  | Assert afc | NoteThat afc -> [afc.hannot_form]
	  | Assume afc | Split afc -> [afc.annot_form]
	  | Havoc hc -> hc.havoc_regions
	  | ProcCall pc -> pc.callee_args
	  | _ -> []
      end
  | Seq cl
  | Choice cl -> List.flatten (List.map find_forms_in_command cl)
  | If {if_condition = ic; if_then = it; if_else = ie} ->
      let it_forms = (find_forms_in_command it) in
      let ie_forms = (find_forms_in_command ie) in
	[ic] @ it_forms @ ie_forms
  | Loop lc ->
      let pre = (find_forms_in_command lc.loop_prebody) in
      let post = (find_forms_in_command lc.loop_postbody) in
	pre @ [lc.loop_test] @ post
  | Return {return_exp = re} ->
      begin
	match re with
	  | Some f -> [f]
	  | None -> []
      end
  | Assuming _ -> Util.fail "find_forms_in_command: \
                             uncaught pattern matching case 'Assuming'"
  | PickAny _ -> Util.fail "find_forms_in_command: \
                            uncaught pattern matching case 'PickAny'"
  | PickWitness _ -> Util.fail "find_forms_in_command: \
                            uncaught pattern matching case 'PickWitness'"
  | Induct _ -> Util.fail "find_forms_in_command: \
                           uncaught pattern matching case 'Induct'"
  | Contradict _ -> Util.fail "find_forms_in_command: \
                               uncaught pattern matching case 'Contradict'"
  | Proof _ -> Util.fail "find_forms_in_command: \
                          uncaught pattern matching case 'Proof'"

(* Return the list of unique boolean formulas with the given formula, excluding boolean variables. *)
let rec get_unique_boolean_formulas (fl : form list) (f : form) : form list =
  match f with
    | App(Const op, _) when (op = Lt || op = Gt || op = LtEq || op = GtEq) ->
	if (List.mem f fl) then fl else (f :: fl)
    | App(Const op, fl0) ->
	List.fold_left get_unique_boolean_formulas fl fl0
    | TypedForm (f, tf) -> get_unique_boolean_formulas fl f
    | _ -> fl

(* Make a unique list of variable comparisons. *)
let rec make_unique_boolean_formulas (fl : form list) (f : form) : form list =
  fl

(* Return the list of free variables in executable code. *)
let rec free_variables (fvs : ident list) = function
  | Basic bc ->
      (match bc.bcell_cmd with
	 | VarAssign ac ->
	     let lhs = ac.assign_lhs in
	     let rhs = FormUtil.fv ac.assign_rhs in
	       Util.union fvs (Util.set_add lhs rhs)
	 | Alloc ac ->
	     Util.set_add ac.alloc_lhs fvs
	 | ArrayAlloc aac ->
	     let lhs = aac.arr_alloc_lhs in
	     let rhs = List.flatten 
	       (List.map FormUtil.fv aac.arr_alloc_dims) in
	       Util.union fvs (Util.set_add lhs rhs)
	 | ProcCall pc ->
	     let fvs0 = match pc.callee_res with
	       | None -> []
	       | Some result -> [result] in
	     let fvs1 = List.flatten
	       (List.map FormUtil.fv pc.callee_args) in
	       Util.union fvs (Util.union fvs0 fvs1)
	 | _ -> fvs)
  | Seq cl 
  | Choice cl -> List.fold_left free_variables fvs cl
  | If ic ->
      let fvs0 = FormUtil.fv ic.if_condition in
      let fvs1 = free_variables (Util.union fvs fvs0) ic.if_then in
	free_variables fvs1 ic.if_else
  | Loop lc ->
      let fvs0 = free_variables fvs lc.loop_prebody in
      let fvs1 = Util.union fvs0 (FormUtil.fv lc.loop_test) in
	free_variables fvs1 lc.loop_postbody
  | Return rc ->
      begin
        match rc.return_exp with
	  | None -> fvs
	  | Some result -> Util.union (FormUtil.fv result) fvs
      end
  | Assuming _ -> Util.fail "free_variables: \
                             uncaught pattern matching case 'Assuming'"
  | PickAny _ -> Util.fail "free_variables: \
                            uncaught pattern matching case 'PickAny'"
  | PickWitness _ -> Util.fail "free_variables: \
                            uncaught pattern matching case 'PickWitness'"
  | Induct _ -> Util.fail "free_variables: \
                           uncaught pattern matching case 'Induct'"
  | Contradict _ -> Util.fail "free_variables: \
                               uncaught pattern matching case 'Contradict'"
  | Proof _ -> Util.fail "free_variables: \
                          uncaught pattern matching case 'Proof'"

let string_of_command (c : command) : string =
  match c with
    | If ic -> "if: " ^ PrintForm.string_of_form ic.if_condition ^ "\n"
    | Loop lc -> "loop: " ^ PrintForm.string_of_form lc.loop_test ^ "\n"
    | _ -> PrintAst.pr_command c

type depend_t = ident * ident list
type depend_tbl_t = (command, depend_t list) Hashtbl.t

let print_depend ((id, ids) : depend_t) : unit =
  let str0 = id ^ " depends on: " in
  let str1 = List.fold_left (fun str id -> str ^ " " ^ id) str0 ids in
    print_string (str1 ^ "\n")

let print_depend_of_cmd (c : command) (deps : depend_t list) : unit =
  let str0 = "The dependencies for:\n" ^ (PrintAst.pr_command c) in
  let str1 = str0 ^ "are:\n" in
    print_string str1;
    List.iter print_depend deps;
    print_string "\n"

let print_depend_tbl (dep_tbl : depend_tbl_t) : unit =
  print_string "*** dependencies ***\n";
  Hashtbl.iter print_depend_of_cmd dep_tbl;
  print_string "********************\n\n"

let depend_compare (d0 : depend_t) (d1 : depend_t) : int =
  String.compare (fst d0) (fst d1)
    
let get_dep 
    (dep_tbl : depend_tbl_t) (id : ident) (c : command) : ident list =
  try let deps = Hashtbl.find dep_tbl c in
    List.assoc id deps
  with Not_found -> [id]

let get_deps (dep_tbl : depend_tbl_t) (c : command) : depend_t list =
  try Hashtbl.find dep_tbl c with Not_found -> []

let dep_of_succ
    (dep_tbl : depend_tbl_t) 
    (succ : command list) 
    (id : ident) : ident list =
  let res = List.map (get_dep dep_tbl id) succ in
    List.fold_left Util.union [] res

let rec merge_deps 
    (d0 : depend_t list) (d1 : depend_t list) : depend_t list =
  match d1 with
    | (id, ids) :: d11 ->
	(try
	   let ids0 = List.assoc id d0 in
	   let ids1 = Util.union ids ids0 in
	   let d00 = List.remove_assoc id d0 in
	     merge_deps ((id, ids1) :: d00) d11
	 with Not_found ->
	   merge_deps ((id, ids) :: d0) d11)
    | [] -> d0

let sort_deps (d : depend_t list) : depend_t list =
  let d0 = List.sort depend_compare d in
    List.map (fun (x, y) -> (x, (List.sort String.compare y))) d0

let propagate_deps 
    (dep_tbl : depend_tbl_t) 
    (c : command)
    (succ : command list) : bool =
  let deps0 = List.map (get_deps dep_tbl) succ in
  let deps1 = sort_deps (List.fold_left merge_deps [] deps0) in
    print_string "NEW:\n";
    List.iter print_depend deps1;
  let deps_old = get_deps dep_tbl c in
    print_string "OLD:\n";
    List.iter print_depend deps_old;
  let result = not (deps1 = deps_old) in
    (if (result) then (* replace previous binding *)
       Hashtbl.replace dep_tbl c deps1);
    result

let update_dep
    (dep_tbl : depend_tbl_t) 
    (c : command)
    (succ : command list) 
    (lhs : ident)
    (rhs : form list) : bool =
  let fvs = List.fold_left Util.union [] (List.map FormUtil.fv rhs) in
  let ids = List.sort String.compare fvs in
  let deps0 = List.map (get_deps dep_tbl) succ in
  let deps1 = List.fold_left merge_deps [] deps0 in
  let deps2 = sort_deps ((lhs, ids) :: (List.remove_assoc lhs deps1)) in
  let deps_old = get_deps dep_tbl c in
  let result = not (deps2 = deps_old) in
    (if (result) then (* replace previous binding *)
       Hashtbl.replace dep_tbl c deps2);
    result

let rec compute_dependencies
    (dep_tbl : depend_tbl_t) 
    (c : command) 
    (succ : command list) : command list =
  match c with
    | Basic bc ->
	(match bc.bcell_cmd with
	   | VarAssign ac ->
	       let lhs = ac.assign_lhs in
	       let rhs = ac.assign_rhs in
	       let _ = update_dep dep_tbl c succ lhs [rhs] in [c]
	   | ProcCall pc ->
	       (match pc.callee_res with
		  | None -> let _ = propagate_deps dep_tbl c succ in [c]
		  | Some lhs -> 
		      let rhs = pc.callee_args in
		      let _ = update_dep dep_tbl c succ lhs rhs in [c])
	   | _ -> let _ = propagate_deps dep_tbl c succ in [c])
    | Seq cl -> 
	let succ0 = List.fold_right (compute_dependencies dep_tbl) cl succ in
	let _ = propagate_deps dep_tbl c succ0 in [c]
    | Choice cl ->
	let succ0 = List.flatten 
	  (List.map (fun x -> compute_dependencies dep_tbl x succ) cl) in
	let _ = propagate_deps dep_tbl c succ0 in [c]
    | If ic ->
	let succ0 = compute_dependencies dep_tbl ic.if_then succ in
	let succ1 = compute_dependencies dep_tbl ic.if_else succ in
	let _ = propagate_deps dep_tbl c (succ0 @ succ1) in [c]
    | Loop lc ->
	let succ0 = Util.set_add lc.loop_prebody succ in
	let succ1 = compute_dependencies dep_tbl lc.loop_postbody succ0 in
	let succ2 = Util.union succ succ1 in
	let succ3 = compute_dependencies dep_tbl lc.loop_prebody succ2 in
	let changed = propagate_deps dep_tbl c succ3 in
	  if changed then
	    compute_dependencies dep_tbl c succ
	  else [c]
    | _ -> let _ = propagate_deps dep_tbl c succ in [c]

let local_dependencies (c : command) : depend_tbl_t =
  let res = Hashtbl.create 100 in
  let _ = compute_dependencies res c [] in
    res

let get_loop_variables (lc : loop_command) : ident list =
  let loop_test = FormUtil.normalize 0 lc.loop_test in
    match loop_test with
      | Var id ->
	  (* Because of the way ast's are constructed, the loop test
	     should always be a boolean variable. This means we need
	     to do some extra work to get at the actual variables that
	     the loop termination depends on. *)
	  let dep_tbl = Hashtbl.create 10 in
	  let prebody = lc.loop_prebody in
	  let _ = compute_dependencies dep_tbl prebody [] in
	    print_depend_tbl dep_tbl;
	    get_dep dep_tbl id prebody
      | _ -> 
	  let msg = "get_loop_variables should not get:\n" ^ 
	    (PrintForm.string_of_form loop_test) in
	    raise (InferenceFailure msg)

let changing_loop_variables 
    (modvars : ident list) (lc : loop_command) : ident list =
  let loopvars = get_loop_variables lc in
    List.filter (fun x -> List.mem x modvars) loopvars

(* Create an appropriately-sized cache for computing the modified
   variables of a loop. *)
let make_new_cache 
    (lc : loop_command) 
    (outer_loops : loop_command list) : modvars_cache_t =
  let num_outer_loops = List.length outer_loops in
  let outermost = if num_outer_loops < 1 then lc 
  else List.nth outer_loops (num_outer_loops - 1) in
  let cache_size = get_loop_depth (Loop outermost) in
    Hashtbl.create cache_size

let make_loop_variable_comparisons
    (proc : proc_def) 
    (lc : loop_command) 
    (outer_loops : loop_command list) : form list =
  let cache = make_new_cache lc outer_loops in
  let modvars = get_modified_variables (Loop lc) cache in
  let loopvars = changing_loop_variables modvars lc in
  let mod_vars_decls, unmod_vars_decls = List.partition 
    (fun (d) -> List.mem d.vd_name modvars) proc.p_locals in
  let rec make_loop_variable_comparisons (comparisons : form list) (f : form) : form list =
    let make_comparisons (id : ident) (ops : constValue list) (d : var_decl) : form list =
      let make_comparison (op : constValue) : form = 
	App(Const op, [(Var id); (Var d.vd_name)]) in
	List.map make_comparison ops
    in
      match f with
	| App(Const op, [(TypedForm ((Var id0), _)); _])
	| App(Const op, [_; (TypedForm ((Var id0), _))])
	| App(Const op, [(Var id0); _])
	| App(Const op, [_; (Var id0)]) when (op = Lt || op = Gt || op = LtEq || op = GtEq) ->
	    print_string ("MATCHED: " ^ (PrintForm.string_of_form f) ^ "\n");
	    begin
	      try
		let decl0 = List.find (fun (d) -> d.vd_name = id0) mod_vars_decls in
		let compare_with = List.filter (fun (d) -> d.vd_type = decl0.vd_type) unmod_vars_decls in
		  print_string ("COMPARE WITH: ");
		  List.iter (fun (x) -> (print_string (x.vd_name ^ " "))) compare_with;
		  print_string ("\n\n");
		  let comparisons0 = List.map (make_comparisons id0 [Lt; Gt; LtEq; GtEq]) compare_with in
		    (List.flatten comparisons0) @ comparisons
	      with Not_found -> comparisons
	    end
	| App(Const op, fl) ->
	    List.fold_left make_loop_variable_comparisons comparisons fl
	| TypedForm (f, tf) -> make_loop_variable_comparisons comparisons f
	| _ -> comparisons
  in
  let outer_loopvars = List.flatten 
    (List.map (changing_loop_variables modvars) outer_loops) in
    print_string ("LOOP VARIABLES: ");
    List.iter (fun (id) -> (print_string (id ^ " "))) loopvars;
    print_string ("\nOUTER LOOP VARIABLES: ");
    List.iter (fun (id) -> (print_string (id ^ " "))) outer_loopvars;
    print_string ("\nUNMODIFIED VARIABLES: ");
    List.iter (fun (x) -> (print_string (x.vd_name ^ " "))) unmod_vars_decls;
    print_string ("\nMODIFIED VARIABLES: ");
    List.iter (fun (x) -> (print_string (x.vd_name ^ " "))) mod_vars_decls;
    print_string ("\n\n");
    print_string ((PrintForm.string_of_form lc.loop_test) ^ "\n");
    let fs = find_forms_in_command (Loop lc) in
    let fbf = List.fold_left get_unique_boolean_formulas [] fs in      
    let loop_variable_comparisons = List.fold_left make_loop_variable_comparisons [] fs in
      print_string ("FORMS:\n");
      List.iter (fun (x) -> (print_string ("\t" ^ (PrintForm.string_of_form x) ^ "\n"))) fs;
      print_string ("UNIQUE:\n");
      List.iter (fun (x) -> (print_string ("\t" ^ (PrintForm.string_of_form x) ^ "\n"))) fbf;
      print_string ("\nCOMPARISONS:\n");
      List.iter (fun (x) -> (print_string ("\t" ^ (PrintForm.string_of_form x) ^ "\n"))) loop_variable_comparisons;
      loop_variable_comparisons

(* Returns a topologically-sorted list of the loops in the
   program. Outer loops occur before the loops they enclose. Loops
   that occur earlier in the code will appear earlier in the list.
*)
let rec get_loops : command -> command list = function
  | Seq cl 
  | Choice cl -> 
      List.flatten (List.map get_loops cl)
  | If {if_then = it; if_else = ie} ->
      (get_loops it) @ (get_loops ie)
  | Loop lc ->
      let pre_loops = (get_loops lc.loop_prebody) in
      let post_loops = (get_loops lc.loop_postbody) in
	(Loop lc) :: (pre_loops @ post_loops)
  | Basic _
  | Return _ -> []
  | Assuming _ -> 
      Util.fail "get_loops: uncaught pattern matching case 'Assuming'"
  | PickAny _ -> 
      Util.fail "get_loops: uncaught pattern matching case 'PickAny'"
  | PickWitness _ -> 
      Util.fail "get_loops: uncaught pattern matching case 'PickWitness'"
  | Induct _ -> 
      Util.fail "get_loops: uncaught pattern matching case 'Induct'"
  | Contradict _ -> 
      Util.fail "get_loops: uncaught pattern matching case 'Contradict'"
  | Proof _ -> 
      Util.fail "get_loops: uncaught pattern matching case 'Proof'"

let loop_iterations = 1

(* Check to see if the formula is trivial. *)
let rec trivial (f : form) : bool =
  (* If all the variables it talks about are old, then it's trivial. *)
  if (List.for_all is_oldname (fv f)) then true
  else match f with
    | Const(BoolConst _) -> true
    | App(Const Eq, [TypedForm(Var x, _); Var y])
    | App(Const Eq, [Var x; TypedForm(Var y, _)])
    | App(Const Eq, [TypedForm(Var x, _); TypedForm(Var y, _)])
    | App(Const Eq, [Var x; Var y]) -> x = y
    | TypedForm(f0, _) -> trivial f0
    | _ -> false

let rec no_field_writes (f : form) : bool =
  match f with
    | Const _
    | Var _ -> true
    | App(Const FieldWrite, _) -> false
    | App(Const Comment, [_; f0])
    | Binder(_, _, f0)
    | TypedForm(f0, _) -> no_field_writes f0
    | App(f0, fs) -> 
	no_field_writes f0 && List.for_all no_field_writes fs

(* Get formulas from program code. *)
let get_code_forms (c : command) : form list =
  let rec get_code_forms_rec : command -> form list = function
    | Basic {bcell_cmd = bc} ->
	begin
	  match bc with
	    | VarAssign {assign_rhs = f} 
	    | Assert {hannot_form = f}
	    | NoteThat {hannot_form = f}
	    | Assume {annot_form = f}
	    | Split {annot_form = f} -> [f]
	    | ArrayAlloc {arr_alloc_dims = fs}
	    | Havoc {havoc_regions = fs}
	    | ProcCall {callee_args = fs} -> fs
	    | _ -> []
	end
    | Seq cl
    | Choice cl ->
	List.flatten (List.map get_code_forms_rec cl)
    | If {if_condition = ic; if_then = it; if_else = ie}  ->
	let fit = get_code_forms_rec it in
	let fie = get_code_forms_rec ie in
	  ic :: (fit @ fie)
    | Loop {loop_prebody = pre; loop_test = test; loop_postbody = post} ->
	let fpre = get_code_forms_rec pre in
	let fpost = get_code_forms_rec post in
	  fpre @ (test :: fpost)
    | Return {return_exp = re} ->
	begin
          match re with
	    | None -> []
	    | Some f -> [f]
        end
    | Assuming _ -> Util.fail "get_code_forms_rec: \
                               uncaught pattern matching case 'Assuming'"
    | PickAny _ -> Util.fail "get_code_forms_rec: \
                              uncaught pattern matching case 'PickAny'"
    | PickWitness _ -> Util.fail "get_code_forms_rec: \
                              uncaught pattern matching case 'PickWitness'"
    | Induct _ -> Util.fail "get_code_forms_rec: \
                             uncaught pattern matching case 'Induct'"
    | Contradict _ -> Util.fail "get_code_forms_rec: \
                                 uncaught pattern matching case 'Contradict'"
    | Proof _ -> Util.fail "get_code_forms_rec: \
                            uncaught pattern matching case 'Proof'"
  in
    Util.remove_dups (get_code_forms_rec c)
      
let rec is_simple_expr (f : form) : bool =
  match f with
      Const _ 
    | Var _ -> true
    | TypedForm(f0, _) 
    | App(Const Comment, [_; f0]) -> is_simple_expr f0
    | _ -> false

let rec form_depth (f : form) : int =
  match f with
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> form_depth f0
    | Const _
    | Var _ -> 0
    | App(f0, fs) ->
	let d0 = form_depth f0 in
	let ds = List.map form_depth fs in
	  1 + (List.fold_left max d0 ds)
    | Binder(_, _, f0) -> 1 + (form_depth f0)

let order_by_depth (f0 : form) (f1 : form) : int =
  (form_depth f0) - (form_depth f1)

let rec form_comp (f0 : form) (f1 : form) : int =
  let const_comp (c0 : constValue) (c1 : constValue) : int =
    match c0, c1 with
      | IntConst i0, IntConst i1 -> i0 - i1
      | BoolConst b0, BoolConst b1 ->
	  if (b0 = b1) then 0
	  else if (b0) then -1 else 1
      | StringConst s0, StringConst s1 ->
	  String.compare s0 s1
      | _ -> String.compare (string_of_const c0) (string_of_const c1) in
  let binder_comp (b0 : binderKind) (b1 : binderKind) : int =
    let binder_int (b : binderKind) : int =
      match b with
	  Forall -> 0
	| Exists -> 1
	| Comprehension -> 2
	| Lambda -> 3 in
      ((binder_int b0) - (binder_int b1)) in
  let rec til_comp (til0 : typedIdent list) (til1 : typedIdent list) : int =
    match til0, til1 with
	[], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | (id0, _) :: tilrest0, (id1, _) :: tilrest1 ->
	  let r0 = String.compare id0 id1 in
	    if (r0 = 0) then
	      til_comp tilrest0 tilrest1
	    else r0 in
    match f0, f1 with
      | App(Const Comment, [_; g0]), App(Const Comment, [_; g1])
      | App(Const Comment, [_; g0]), g1
      | g0, App(Const Comment, [_; g1])
      | TypedForm(g0, _), TypedForm(g1, _) 
      | TypedForm(g0, _), g1
      | g0, TypedForm(g1, _) -> form_comp g0 g1
      | Var id0, Var id1 -> String.compare id0 id1
      | Var _, _ -> -1
      | _, Var _ -> 1
      | App(g0, gs0), App(g1, gs1) ->
	  let r0 = form_comp g0 g1 in
	    if (r0 = 0) then
	      form_comp_list gs0 gs1
	    else r0
      | App _, _ -> -1
      | _, App _ -> 1
      | Binder(b0, til0, g0), Binder(b1, til1, g1) ->
	  let r0 = binder_comp b0 b1 in
	    if (r0 = 0) then
	      let r1 = til_comp til0 til1 in
		if (r1 = 0) then
		  form_comp g0 g1
		else r1
	    else r0
      | Binder _, _ -> -1
      | _, Binder _ -> 1
      | Const c0, Const c1 -> const_comp c0 c1
and form_comp_list (fs0 : form list) (fs1 : form list) : int =
  match fs0, fs1 with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | f0 :: frest0, f1 :: frest1 ->
	let r0 = form_comp f0 f1 in
	  if (r0 = 0) then
	    form_comp_list frest0 frest1
	  else r0

let symmetric (c : constValue) : bool =
  match c with
      Eq | MetaEq | Or | And | MetaAnd 
    | Disjoint | Cap | Cup | Seteq | Plus | Mult
	  -> true
    | _ -> false

(* Given a list of formulas of the same type, return the type if found. *)
let rec get_typeForm (fs : form list) : typeForm option =
  match fs with
    | [] -> None
    | f :: fs0 ->
	match f with
	  | TypedForm(_, tf) -> Some tf
	  | _ -> get_typeForm fs0

let apply_typeForm (tf : typeForm) (f : form) : form =
  match f with
    | Const _
    | TypedForm _ -> f
    | _ -> TypedForm(f, tf)

let get_and_apply_typeForm (fs : form list) : form list =
  match get_typeForm fs with
    | None -> fs
    | Some tf -> List.map (apply_typeForm tf) fs
    
(* Some basic normalizations to make it easier to identify duplicate
   formulas. Should be applied after remove_comments. *)
let rec normalize (f0 : form) : form =
  match f0 with
    | App(Const op, fs) when (symmetric op) ->
	let fs0 = List.map normalize fs in
	let fs1 = List.sort form_comp fs0 in
	let fs2 = get_and_apply_typeForm fs1 in
	  App(Const op, fs2)
    | App(f1, fs) ->
	App((normalize f1), (List.map normalize fs))
    | Binder(b, til, f1) ->
	Binder(b, til, (normalize f1))
    | TypedForm(f1, ty) ->
	TypedForm((normalize f1), ty)
    | _ -> f0

let eval (op : constValue) (i0 : int) (i1 : int) : form =
  match op with
    | Eq -> Const (BoolConst (i0 = i1))
    | Lt -> Const (BoolConst (i0 < i1))
    | Gt -> Const (BoolConst (i0 > i1))
    | LtEq -> Const (BoolConst (i0 <= i1))
    | GtEq -> Const (BoolConst (i0 >= i1))
    | Plus -> Const (IntConst (i0 + i1))
    | Minus -> Const (IntConst (i0 - i1))
    | Mult -> Const (IntConst (i0 * i1))
    | Div -> Const (IntConst (i0 / i1))
    | _ -> App(Const op, [Const (IntConst i0); Const (IntConst i1)])

(* Should be applied on normalized formulas. *)
let rec simplify (f : form) : form =
  match f with
    | App(Const And, fs) ->
	smk_and (List.map simplify fs)
    | App(Const Or, fs) ->
	smk_or (List.map simplify fs)
    | App(Const Not, [TypedForm(Const (BoolConst true), _)])
    | App(Const Not, [Const (BoolConst true)]) -> mk_false
    | App(Const Not, [TypedForm(Const (BoolConst false), _)])
    | App(Const Not, [Const (BoolConst false)]) -> mk_true
    | App(Const op, [TypedForm(Const (IntConst x), _); TypedForm(Const (IntConst y), _)]) -> 
	eval op x y
    | App(Const Minus, [TypedForm(Var x, TypeApp(TypeInt, [])); TypedForm(Var y, _)]) 
	when (x = y) -> 
	Const (IntConst 0)
    | App(Const Diff, [TypedForm(Var x, _); TypedForm(Var y, _)]) 
    | App(Const Minus, [TypedForm(Var x, TypeApp(TypeSet, _)); TypedForm(Var y, _)])
	when (x = y) -> 
	Const EmptysetConst
    | App(Const Cup, [TypedForm(Const EmptysetConst, _); f0])
    | App(Const Plus, [TypedForm(Const (IntConst 0), _); f0])
    | App(Const Minus, [f0; TypedForm(Const (IntConst 0), _)]) ->
	simplify f0
    | App(Const Elem, [_; Const EmptysetConst])
    | App(Const Elem, [_; TypedForm(Const EmptysetConst, _)]) ->
	mk_false
    | App(Const Lt, [TypedForm(Var x, _); TypedForm(Var y, _)])
    | App(Const Gt, [TypedForm(Var x, _); TypedForm(Var y, _)]) when (x = y) ->
	mk_false
    | App(Const Impl, [_; TypedForm(Const (BoolConst true), _)])
    | App(Const Impl, [_; Const (BoolConst true)])
    | App(Const Impl, [TypedForm(Const (BoolConst false), _); _])
    | App(Const Impl, [Const (BoolConst false); _]) ->
	mk_true
    | App(Const Eq, [TypedForm(f0, _); TypedForm(f1, _)])
    | App(Const Eq, [TypedForm(f0, _); f1])
    | App(Const Eq, [f0; TypedForm(f1, _)])
    | App(Const Eq, [f0; f1]) when f0 = f1 ->
	mk_true
    | App(Const Eq, [TypedForm(Var x, _); TypedForm(Var y, _)])
    | App(Const LtEq, [TypedForm(Var x, _); TypedForm(Var y, _)])
    | App(Const GtEq, [TypedForm(Var x, _); TypedForm(Var y, _)]) when (x = y) ->
	mk_true
    | App(Const op, [TypedForm(Const (BoolConst true), _); f0])
    | App(Const op, [Const (BoolConst true); f0])
    | App(Const op, [f0; TypedForm(Const (BoolConst true), _)])
    | App(Const op, [f0; Const (BoolConst true)])
	when (op = Eq || op = Impl) -> 
	simplify f0
    | App(Const Mult, [TypedForm(Const (IntConst 1), _); f0]) ->
	simplify f0
    | App(Const Mult, [TypedForm(Const (IntConst 0), _); _]) ->
	Const (IntConst 0)
    | App(Const Impl, [f0; TypedForm(Const (BoolConst false), _)])
    | App(Const Impl, [f0; Const (BoolConst false)])
    | App(Const Eq, [TypedForm(Const (BoolConst false), _); f0])
    | App(Const Eq, [Const (BoolConst false); f0])
    | App(Const Eq, [f0; TypedForm(Const (BoolConst false), _)])
    | App(Const Eq, [f0; Const (BoolConst false)]) ->
	simplify (smk_not f0)
    | App(Const Elem, [f0; App(Const FiniteSetConst, [f1])])
    | App(Const Elem, [f0; TypedForm(App(Const FiniteSetConst, [f1]), _)]) ->
	simplify (App(Const Eq, [f0; f1]))
    | App(f0, fs) ->
	App((simplify f0), (List.map simplify fs))
    | Binder(b, til, f0) ->
	Binder(b, til, (simplify f0))
    | TypedForm(f0, ty) ->
	TypedForm((simplify f0), ty)
    | _ -> f

(* iterate to a fixed point *)
let rec simplify_until (f : form) : form =
  let f0 = simplify f in
    if f0 = f then f0
    else simplify_until f0

(* Remove top-level comments and types. *)
let rec reduce_f (f : form) : form =
  match f with
    | TypedForm(f0, _)
    | App(Const Comment, [_; f0]) -> reduce_f f0
    | _ -> f

let clean_up (f : form) : form =
  reduce_f 
    (normalize (simplify_until (normalize (remove_comments f))))

(* Find expressions of the given type in f. *)
let exprs_of_type (tf : typeForm) (f : form) : form list =
  let rec exprs_of_type_rec (tf : typeForm) (el : form list) (f : form) : form list =
      match f with
	| App(Const op, fs) when 
	    ((tf = TypeApp (TypeInt, [])) && 
	       (op = Plus || op = Minus || op = Mult || op = Div)) ->
	    let el0 = if (List.for_all is_simple_expr fs) then  (el @ [f]) else el in
	      List.fold_left (exprs_of_type_rec tf) el0 fs
	| App(Const Eq, [TypedForm(f0, tf0); f1])
	| App(Const Eq, [f1; TypedForm(f0, tf0)]) when (tf0 = tf) ->
	  let el0 = if (is_simple_expr f0) then el else (el @ [f0]) in
	  let el1 = exprs_of_type_rec tf el0 f0 in
	  let el2 = if (is_simple_expr f1) then el1 else (el1 @ [f1]) in
	    exprs_of_type_rec tf el2 f1
	| App(f0, fs) ->
	  let el0 = exprs_of_type_rec tf el f0 in
	    List.fold_left (exprs_of_type_rec tf) el0 fs
	| Binder(_, _, f0) ->
	    exprs_of_type_rec tf el f0
	| _ -> el in
    Util.remove_dups (exprs_of_type_rec tf [] f)

(* Returns true if c is an operator whose arguments are of the same
   type as its result. *)
let ec_preserving_op (c : constValue) : bool =
  match c with
    | MetaEq | MetaAnd | Or | And | Not | Iff 
    | UMinus | Plus | Minus | Mult | Div | Mod | Old -> true
    | _ -> false

(* Returns true if c is an operator of multiple arguments of the same
   type. *)
let same_ec_args (c : constValue) : bool =
  match c with
    | Eq | MetaEq
    | Or | And | MetaAnd | Impl | MetaImpl | Iff | Disjoint 
    | Lt | Gt | LtEq | GtEq
    | Cap | Cup | Diff 
    | Subseteq | Subset | Seteq
    | Plus | Minus | Mult | Div | Mod -> true
    | _ -> false

let print_form (f : form) : unit =
  print_string ((PrintForm.string_of_form f) ^ "\n")

let mk_freeExpr (f : form) : expr_t =
  FreeExpr f

let string_of_expr (e : expr_t) : string =
  match e with 
    | BoundExpr (f, til) ->
	"[BE]: " ^ (PrintForm.string_of_form f) ^ 
	  " [" ^ (PrintForm.wr_bindings til) ^ "]"
    | FreeExpr f ->
	"[FE]: " ^ (PrintForm.string_of_form f)

let print_expr (e : expr_t) : unit =
  print_string ((string_of_expr e) ^ "\n")

let expr_by_depth (e0 : expr_t) (e1 : expr_t) : int =
  match e0, e1 with
    | BoundExpr (f0, til0), BoundExpr (f1, til1) ->
	let res = order_by_depth f0 f1 in
	  if res = 0 then 
	    (List.length til0) - (List.length til1)
	  else res
    | FreeExpr f0, FreeExpr f1 -> order_by_depth f0 f1
    | BoundExpr _, _ -> -1
    | _ -> 1

(* Primitives for equivalent classes *)

let print_equiv_classes (ecs : equiv_classes_t) : unit =
  print_string ("\n\nEQUIVALENT CLASSES:\n\n");
  List.iter (fun (fs) ->
	       print_string ("BEGIN\n");
	       List.iter print_expr (List.sort expr_by_depth fs);
	       print_string ("END\n\n")) ecs

(* Find the equivalence class of the given formula. *)
let get_equiv_class 
    (e : expr_t) 
    (ecs : equiv_classes_t) : equiv_class_t * equiv_classes_t =
  let ecs0, ecs_rest = List.partition (List.mem e) ecs in
    match ecs0 with
      | [] -> [e], ecs_rest
      | [ec0] -> ec0, ecs_rest
      | _ -> let err = "There are multiple equivalence classes for " ^ 
	  (string_of_expr e) in
	  raise (InferenceFailure err)
	  
(* Add f to the given equivalence class. *)
let add_to_equiv_class 
    ((ec : equiv_class_t), (ecs : equiv_classes_t))
    (e : expr_t) : equiv_class_t * equiv_classes_t =
  if (List.mem e ec) then 
    ec, ecs (* already in the same equivalence class *)
  else
    let ec0, ecr0 = get_equiv_class e ecs in
      (ec @ ec0), ecr0 (* merge the two equivalence classes *)

let get_equivalent (ecs : equiv_classes_t) (e : expr_t) : expr_t list =
  let ec, _ = get_equiv_class e ecs in
    List.filter (fun x -> x <> e) ec

let make_equivalent
    (ecs : equiv_classes_t) 
    (e0 : expr_t) 
    (e1 : expr_t) : equiv_classes_t =
  let ec, ecr = add_to_equiv_class (get_equiv_class e0 ecs) e1 in
    (ec :: ecr)

let make_all_equivalent 
    (ecs : equiv_classes_t) (es : expr_t list) : equiv_classes_t =
  match es with
    | [] | [_] -> ecs
    | e :: er -> 
	let ec_e = get_equiv_class e ecs in
	let ec, ecr = List.fold_left add_to_equiv_class ec_e er in
	  (ec :: ecr)

let print_context (c : context_t) : unit =
  match c with
    | SetElement f -> 
	print_string 
	  ("elementOf: " ^ (PrintForm.string_of_form f) ^ "\n");
    | Arg (i, f) ->
	print_string 
	  ("argument " ^ (string_of_int i) ^ " of: " ^ 
	     (PrintForm.string_of_form f) ^ "\n");
    | Field f ->
	print_string
	  ("hasField " ^ (PrintForm.string_of_form f) ^ "\n")

let print_context_map (cm : context_map_t) : unit =
  Hashtbl.iter 
    (fun x y -> 
       print_context x;
       List.iter print_expr y;
       print_string "\n") cm

let add_to_context_map 
    (cm : context_map_t) (c : context_t) (e : expr_t) : unit =
  try
    let es = Hashtbl.find cm c in
      Hashtbl.replace cm c (Util.set_add e es)
  with Not_found -> Hashtbl.add cm c [e]

let expr_of_form (sc : typedIdent list) (f : form) : expr_t =
  let fvs = FormUtil.fv f in
  let sc = List.filter (fun (x, _) -> List.mem x fvs) sc in
    if sc <> [] then
      BoundExpr (f, sc)
    else FreeExpr f

let current_scope 
    (os : typedIdent list) (is : typedIdent list) : typedIdent list =
  (List.filter (fun (x, _) -> not (List.mem_assoc x is)) os) @ is
       
let rec collect_contexts 
    (sc : typedIdent list) (cm : context_map_t) (f : form) : unit =
  match f with
    | TypedForm(f0, _)
    | App(Const Comment, [_; f0]) ->
	collect_contexts sc cm f0
    | Binder(_, til, f0) ->
	collect_contexts (current_scope sc til) cm f0
    | App(Const FieldRead, [TypedForm(f0, _); TypedForm(f1, _)])
    | App(Const FieldRead, [TypedForm(f0, _); f1])
    | App(Const FieldRead, [f0; TypedForm(f1, _)])
    | App(Const FieldRead, [f0; f1]) ->
	add_to_context_map cm (Field f0) (expr_of_form sc f1);
	collect_contexts sc cm f0;
	collect_contexts sc cm f1
    | App(Const FieldWrite, [TypedForm(f0, _); TypedForm(f1, _); f2])
    | App(Const FieldWrite, [TypedForm(f0, _); f1; f2])
    | App(Const FieldWrite, [f0; TypedForm(f1, _); f2])
    | App(Const FieldWrite, [f0; f1; f2]) ->
	add_to_context_map cm (Field f0) (expr_of_form sc f1);
	collect_contexts sc cm f0;
	collect_contexts sc cm f1;
	collect_contexts sc cm f2
    | App(f0, fs) ->
	collect_contexts sc cm f0;
	List.iter (collect_contexts sc cm) fs
    | _ -> ()

let rec ident_of_form (f : form) : ident =
  match f with
    | Var v -> v
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> ident_of_form f0
    | _ -> let err = "ident_of_form did not expect " ^
	(PrintForm.string_of_form f) in
	raise (InferenceFailure err)
	  
let is_classname (env : inference_env_t) (f : form) : bool =
  try
    let id = ident_of_form f in
    let id = if (FormUtil.is_oldname id) then
      (FormUtil.unoldname id) else id in
      List.mem id env.ie_classes
  with InferenceFailure _ -> false

let is_alloc_obj (f : form) : bool =
  try
    let id = ident_of_form f in
    let id = if (FormUtil.is_oldname id) then
      (FormUtil.unoldname id) else id in
      id = all_alloc_objs
  with InferenceFailure _ -> false
    
let is_tmp = Javajast.is_tmp

let is_not_tmp (s : string) : bool =
  not (is_tmp s)

let contains_non_tmp (f : form) : bool =
  List.exists is_not_tmp (FormUtil.fv f)

let non_tmp_only (f : form) : bool =
  List.for_all is_not_tmp (FormUtil.fv f)

let no_ref_to_result (f : form) : bool =
  not (List.mem Ast.result_var (FormUtil.fv f))

let rec not_type_check (env : inference_env_t) (f : form) : bool =
  match f with
    | App(Const Elem, [_; f1]) -> not (is_classname env f1)
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> not_type_check env f0
    | _ -> true

let rec not_alloc_check (f : form) : bool =
  match f with
    | App(Const Elem, [_; f1]) -> not (is_alloc_obj f1)
    | App(Const Comment, [_; f0])
    | TypedForm(f0, _) -> not_alloc_check f0
    | _ -> true

let no_ref_to_non_fvs (ids : ident list) (f : form) : bool =
  List.for_all (fun x -> List.mem x ids) (FormUtil.fv f)

(* Puts f in the given equivalence class and recursively descends f to
   compute more equivalence classes. *)
let rec make_equiv
    (sc : typedIdent list)
    ((ec : equiv_class_t), (ecs : equiv_classes_t)) 
    (f : form) : equiv_class_t * equiv_classes_t =
  match f with
    | Var _
    | Const _ -> add_to_equiv_class (ec, ecs) (expr_of_form sc f)
    | TypedForm(f0, _) 
    | App(Const Comment, [_; f0]) -> 
	make_equiv sc (ec, ecs) f0
    | App(Const And, fs) ->
	(* We want to split conjunctions up. *)
	List.fold_left (make_equiv sc) (ec, ecs) fs
    | App(Const op, fs) when (ec_preserving_op op) ->
	let ec0, ecs0 = 
	  add_to_equiv_class (ec, ecs) (expr_of_form sc f) in
	  List.fold_left (make_equiv sc) (ec0, ecs0) fs
    | App(Const op, f0 :: fs) when (same_ec_args op) ->
	let e_f = expr_of_form sc f in
	let ec0, ecs0 = add_to_equiv_class (ec, ecs) e_f in
	let ec1, ecs1 = make_equiv sc ([], (ec0 :: ecs0)) f0 in
	let ec2, ecs2 = List.fold_left (make_equiv sc) (ec1, ecs1) fs in
	  get_equiv_class e_f (ec2 :: ecs2)
    | App(Const Elem, [f0; f1]) ->
	let f00 = mk_singleton f0 in
	let e_f = expr_of_form sc f in
	let ec0, ecs0 = add_to_equiv_class (ec, ecs) e_f in
	let ec1, ecs1 = make_equiv sc ([], (ec0 :: ecs0)) f00 in
	let ec2, ecs2 = make_equiv sc (ec1, ecs1) f1 in
	  get_equiv_class e_f (ec2 :: ecs2)
    | App(f0, fs) ->
	let e_f = expr_of_form sc f in
	let ec0, ecs0 = add_to_equiv_class (ec, ecs) e_f in
	  get_equiv_class e_f (descend sc (ec0 :: ecs0) fs)
    | Binder(Comprehension, til, f0) ->
	let e_f = expr_of_form sc f in
	let ec0, ecs0 = add_to_equiv_class (ec, ecs) e_f in
	let sc' = current_scope sc til in
	let ec1, ecs1 = make_equiv sc' ([], (ec0 :: ecs0)) f0 in
          get_equiv_class e_f (ec1 :: ecs1)
    | Binder(b, til, f0) ->
	let e_f = expr_of_form sc f in
	let sc' = current_scope sc til in
	  make_equiv sc' (add_to_equiv_class (ec, ecs) e_f) f0
and descend 
    (sc : typedIdent list) 
    (ecs : equiv_classes_t) 
    (fs : form list) : equiv_classes_t =
  match fs with
    | [] -> ecs
    | f0 :: fs0 ->
	let ec0, ecs0 = make_equiv sc ([], ecs) f0 in
	  descend sc (ec0 :: ecs0) fs0

let clean_up_and_make_equiv
    ((ec : equiv_class_t), (ecs : equiv_classes_t)) 
    (f : form) : equiv_class_t * equiv_classes_t =
  make_equiv [] (ec, ecs) (clean_up f)

(* Compute equivalence classes for the given vardef. *)
let compute_equiv_vardef 
    (ecs : equiv_classes_t) (vd : Ast.specvar_def) : equiv_classes_t =
  let ec0, ecs0 = clean_up_and_make_equiv ([], ecs) (Var (fst vd)) in
  let ec1, ecs1 = clean_up_and_make_equiv (ec0, ecs0) (snd vd) in
    ec1 :: ecs1

(* Compute equivalence classes for the given formula. *)
let compute_equiv (ecs : equiv_classes_t) (f : form) : equiv_classes_t =
  let ec0, ecs0 = clean_up_and_make_equiv ([], ecs) f in
    ec0 :: ecs0

let rec reduce_to_formulas : command -> form list = function
  | Basic {bcell_cmd = bc} ->
      (match bc with
	 | VarAssign {assign_lhs = lhs; assign_rhs = rhs} ->
	     [mk_eq(mk_var lhs, rhs)]
	 | ArrayAlloc {arr_alloc_dims = [f]} 
	 | Assert {hannot_form = f} 
	 | NoteThat {hannot_form = f} 
	 | Assume {annot_form = f} 
	 | Split {annot_form = f} -> [f]
	 | Havoc {havoc_regions = fs}
	 | ProcCall {callee_args = fs} -> fs
	 | _ -> [])
  | Seq cl 
  | Choice cl -> List.flatten (List.map reduce_to_formulas cl)
  | If {if_condition = f; if_then = c0; if_else = c1}
  | Loop {loop_prebody = c0; loop_test = f; loop_postbody = c1} ->
      f :: (reduce_to_formulas c0) @ (reduce_to_formulas c1)
  | Return {return_exp = fo} ->
      begin
        match fo with
	  | None -> []
	  | Some f -> [mk_eq(mk_var result_var, f)]
      end
  | Assuming _ -> Util.fail "reduce_to_formulas: \
                             uncaught pattern matching case 'Assuming'"
  | PickAny _ -> Util.fail "reduce_to_formulas: \
                            uncaught pattern matching case 'PickAny'"
  | PickWitness _ -> Util.fail "reduce_to_formulas: \
                            uncaught pattern matching case 'PickWitness'"
  | Induct _ -> Util.fail "reduce_to_formulas: \
                           uncaught pattern matching case 'Induct'"
  | Contradict _ -> Util.fail "reduce_to_formulas: \
                               uncaught pattern matching case 'Contradict'"
  | Proof _ -> Util.fail "reduce_to_formulas: \
                          uncaught pattern matching case 'Proof'"


(* Compute equivalence classes of variables and expressions in c. *)
let make_equiv_classes (c : command) : equiv_classes_t =
  let rec equiv_classes_rec (ecs : equiv_classes_t)
      : command -> equiv_classes_t = function
        | Basic {bcell_cmd = bc} ->
	    (match bc with
	       | VarAssign {assign_lhs = id; assign_rhs = f} ->
		   let e_v = FreeExpr (Var id) in
		   let ec0, ecs_rest = get_equiv_class e_v ecs in
		   let ec1, ecs1 = clean_up_and_make_equiv (ec0, ecs_rest) f in
		     ec1 :: ecs1
	       | ArrayAlloc {arr_alloc_dims = fs}
	       | Havoc {havoc_regions = fs}
	       | ProcCall {callee_args = fs} -> descend [] ecs fs
	       | Assert {hannot_form = f}
	       | NoteThat {hannot_form = f}
	       | Assume {annot_form = f}
	       | Split {annot_form = f} -> 
		   let ec0, ecs0 = clean_up_and_make_equiv ([], ecs) f in
		     ec0 :: ecs0
	       | _ -> ecs)
        | Seq cl 
        | Choice cl ->
	    List.fold_left equiv_classes_rec ecs cl
        | If {if_condition = f; if_then = it; if_else = ie} ->
	    let ecs0 = descend [] ecs [(clean_up f)] in
	    let ecs1 = equiv_classes_rec ecs0 it in
	      equiv_classes_rec ecs1 ie
        | Loop {loop_prebody = pre; loop_test = f; loop_postbody = post} ->
	    let ecs0 = equiv_classes_rec ecs pre in
	    let ecs1 = descend [] ecs0 [(clean_up f)] in
	      equiv_classes_rec ecs1 post
        | Return {return_exp = fo} ->
	    begin
              match fo with
	        | None -> ecs
	        | Some f -> 
		    let e_v = FreeExpr (Var Ast.result_var) in
		    let ec0, ecs0 = get_equiv_class e_v ecs in
		    let ec1, ecs1 = clean_up_and_make_equiv (ec0, ecs0) f in
		      ec1 :: ecs1
            end
        | Assuming _ -> Util.fail "equiv_classes_rec: \
                                   uncaught pattern matching case 'Assuming'"
        | PickAny _ -> Util.fail "equiv_classes_rec: \
                                  uncaught pattern matching case 'PickAny'"
        | PickWitness _ -> Util.fail "equiv_classes_rec: \
                                  uncaught pattern matching case 'PickWitness'"
        | Induct _ -> Util.fail "equiv_classes_rec: \
                                 uncaught pattern matching case 'Induct'"
        | Contradict _ -> Util.fail "equiv_classes_rec: \
                                     uncaught pattern matching case 'Contradict'"
	| Proof _ -> Util.fail "equiv_classes_rec: \
                                uncaught pattern matching case 'Proof'"
  in
    equiv_classes_rec [] c

let basic_equivalence 
    (c : command) 
    (fs : form list) 
    (vds : Ast.specvar_def list) : equiv_classes_t =
  let ecs0 = make_equiv_classes c in
  let ecs1 = List.fold_left compute_equiv ecs0 fs in
  let ecs2 = List.fold_left compute_equiv_vardef ecs1 vds in
    ecs2

let incorporate_context 
    (ecs : equiv_classes_t) (cm : context_map_t) : equiv_classes_t =
  Hashtbl.fold (fun _ es ecs -> make_all_equivalent ecs es) cm ecs

let form_of_svs (svs : Ast.specvar_def list) : form list =
  List.map (fun (x, y) -> mk_eq ((Var x), y)) svs

let fvs_of_form (ids : ident list) (f : form) : ident list =
  Util.union ids (FormUtil.fv f)

(* Compute the free variables of the given command. *)
let fvs_of_cmd (c : command) : ident list =
  let rec fvs_of_cmd_rec (ids : ident list) (c : command) : ident list =
    match c with 
      | Basic {bcell_cmd = bc} ->
	  (match bc with
	     | VarAssign {assign_lhs = id; assign_rhs = f} ->
		 let ids0 = Util.set_add id ids in
		   fvs_of_form ids0 f
	     | ArrayAlloc {arr_alloc_dims = fs}
	     | Havoc {havoc_regions = fs}
	     | ProcCall {callee_args = fs} ->
		 List.fold_left fvs_of_form ids fs
	     | Assert {hannot_form = f}
	     | NoteThat {hannot_form = f}
	     | Assume {annot_form = f}
	     | Split {annot_form = f} -> fvs_of_form ids f
	     | _ -> ids)
      | Seq cl 
      | Choice cl ->
	  List.fold_left fvs_of_cmd_rec ids cl
      | If {if_condition = f; if_then = c0; if_else = c1}
      | Loop {loop_prebody = c0; loop_test = f; loop_postbody = c1} ->
	  let ids0 = fvs_of_form ids f in
	  let ids1 = fvs_of_cmd_rec ids0 c0 in
	    fvs_of_cmd_rec ids1 c1
      | Return {return_exp = fo} ->
          begin
	    match fo with
	      | None -> ids
	      | Some f -> fvs_of_form ids f
          end
      | Assuming _ -> Util.fail "fvs_of_cmd_rec: \
                                 uncaught pattern matching case 'Assuming'"
      | PickAny _ -> Util.fail "fvs_of_cmd_rec: \
                                uncaught pattern matching case 'PickAny'"
      | PickWitness _ -> Util.fail "fvs_of_cmd_rec: \
                                uncaught pattern matching case 'PickWitness'"
      | Induct _ -> Util.fail "fvs_of_cmd_rec: \
                               uncaught pattern matching case 'Induct'"
      | Contradict _ -> Util.fail "fvs_of_cmd_rec: \
                                   uncaught pattern matching case 'Contradict'"
      | Proof _ -> Util.fail "fvs_of_cmd_rec: \
                              uncaught pattern matching case 'Proof'"
  in
    fvs_of_cmd_rec [] c
      
let fvs_of_vd (ids : ident list) (vd : Ast.specvar_def) : ident list =
  let ids0 = Util.set_add (fst vd) ids in
    Util.union ids0 (FormUtil.fv (snd vd))
      
let print_results (label : string) (fs : form list) : unit =
  print_string ("\n\n" ^ label ^ ":\n");
  List.iter print_form fs;
  print_string ("\n");
  flush_all ()

let rec add_if_not_dup lst elm =
  match lst with
      [] -> [elm]
    | elm0 :: rest ->
	if (elm0 = elm) then lst
	else elm0 :: (add_if_not_dup rest elm)

(* Return the list of constant values in the formula. *)
let rec get_consts_rec 
    (cl : constValue list) (f : form) : constValue list =
  match f with
    | Const c ->
	(match c with
	   | IntConst _
	   | BoolConst _
	   | NullConst
	   | StringConst _
	   | EmptysetConst -> Util.set_add c cl
	   | _ -> cl)
    | App(f0, fs) ->
	let res0 = get_consts_rec cl f0 in
	  List.fold_left get_consts_rec res0 fs
    | Binder(_, _, f0)
    | TypedForm(f0, _) ->
	get_consts_rec cl f0
    | _ -> cl
    
let get_consts = get_consts_rec []

type cSubstMap = (constValue * form) list

(* Substitute constant values in the formula according to sm. *)
let subst_const (sm : cSubstMap) (f : form) : form =
  let rec subst_const_rec (f : form) : form =
    match f with
	Const c ->
	  begin
	    try
	      List.assoc c sm
	    with Not_found -> f
	  end
      | App(f0, fs) ->
	  App((subst_const_rec f0), (List.map subst_const_rec fs))
      | Binder(b, til, f0) ->
	  Binder(b, til, (subst_const_rec f0))
      | TypedForm(f0, ty) ->
	  TypedForm((subst_const_rec f0), ty)
      | _ -> f in
    subst_const_rec f

let get_templates (proc : proc_def) : form list =
  let rec get_templates_rec (fs : form list) : command -> form list = function
    | Basic {bcell_cmd = bc} ->
	(match bc with
	   | Assert {hannot_form = f}
	   | NoteThat {hannot_form = f}
	   | Assume {annot_form = f}
	   | Split {annot_form = f} ->
	       Util.union fs (FormUtil.get_conjuncts f)
	   | _ -> fs)
    | Seq cl
    | Choice cl ->
	List.fold_left get_templates_rec fs cl
    | If {if_then = it; if_else = ie} ->
	let fs0 = get_templates_rec fs it in
	  get_templates_rec fs0 ie
    | Loop {loop_prebody = pre; loop_postbody = post} ->
	let fs0 = get_templates_rec fs pre in
	  get_templates_rec fs0 post
    | Return _ -> fs
    | Assuming _ -> Util.fail "get_templates_rec: \
                               uncaught pattern matching case 'Assuming'"
    | PickAny _ -> Util.fail "get_templates_rec: \
                              uncaught pattern matching case 'PickAny'"
    | PickWitness _ -> Util.fail "get_templates_rec: \
                              uncaught pattern matching case 'PickWitness'"
    | Induct _ -> Util.fail "get_templates_rec: \
                             uncaught pattern matching case 'Induct'"
    | Contradict _ -> Util.fail "get_templates_rec: \
                                 uncaught pattern matching case 'Contradict'"
    | Proof _ -> Util.fail "get_templates_rec: \
                            uncaught pattern matching case 'Proof'"
  in
    get_templates_rec [] proc.p_body

(* For each loop: *)
(* Step 1: Create a set of candidate invariants. *)
(* Step 2: For each invariant, test to see if implied. *)
(* Step 3: Take the conjunction of the candidate invariants that passed Step 3. *)
(* Step 4: Let the result of Step 4 be the loop invariant. *)
(* Step 5: If end of program is reached, run standard vcgen. Otherwise goto Step 1. *)

(* Heuristics for creating candidate invariants. *)

(* TEMPLATES *)
(* 1. Module invariant. *)
(* 2. Procedure precondition. *)
(* 3. Procedure postcondition. *)

(* HEURISTICS *)
(* 4. If inner loop, relate inner and outer loop variables using <, <= ,> and >=. *)
(* 5. Replace one of the bounds in the template with the loop variable. *)

let rec handle_next_loop 
    (handler : loop_command -> command list -> unit)
    (outer_loops : command list)
    (c : command) : unit =
  match c with
    | Seq cl 
    | Choice cl -> 
	List.iter (handle_next_loop handler outer_loops) cl
    | If {if_then = it; if_else = ie} ->
	handle_next_loop handler outer_loops it;
	handle_next_loop handler outer_loops ie
    | Loop lc ->
	handler lc outer_loops;
	handle_next_loop handler (c :: outer_loops) lc.loop_prebody;
	handle_next_loop handler (c :: outer_loops) lc.loop_postbody
    | Basic _
    | Return _ -> ()
    | Assuming _ -> Util.fail "handle_next_loop: \
                               uncaught pattern matching case 'Assuming'"
    | PickAny _ -> Util.fail "handle_next_loop: \
                              uncaught pattern matching case 'PickAny'"
    | PickWitness _ -> Util.fail "handle_next_loop: \
                              uncaught pattern matching case 'PickWitness'"
    | Induct _ -> Util.fail "handle_next_loop: \
                             uncaught pattern matching case 'Induct'"
    | Contradict _ -> Util.fail "handle_next_loop: \
                                 uncaught pattern matching case 'Contradict'"
    | Proof _ -> Util.fail "handle_next_loop: \
                            uncaught pattern matching case 'Proof'"

let infer (lc : loop_command) (outer_loops : command list) : unit =
  print_string ("Inferring loop invariant for:\n\t");
  print_string ((PrintAst.pr_command (Loop lc)) ^ "\n");
  let ids = get_loop_variables lc in
    List.iter (fun x -> print_string ("loop variable: " ^ x ^ "\n")) ids

let check_count = ref 0
let clear_check_count () : unit = check_count := 0
let incr_check_count () : unit = check_count := !check_count + 1

let try_executing_sp
    (env : inference_env_t) (hist : history_t) (f : form) : bool =
  let lc = hist.h_loop in
  let original_li = lc.loop_inv in (* save original loop invariant *)
  let _ = lc.loop_inv <- Some f in
  let _ = debug_msg ("SP: " ^ (PrintForm.string_of_form f) ^ "\n\n") in
  let result = Strongest_postcondition.sp_unrolled env.ie_precondition 
    env.ie_proc.p_body env.ie_iterations in
    lc.loop_inv <- original_li; (* restore original loop invariant *)
    result

let poor_candidate (hist : history_t) (f : form) : bool =
  let inv = smk_and hist.h_passed in (* the loop invariant so far *)
  let result = trivial f || Decider.valid f || 
    Decider.valid (smk_not f) || 
    ((not (hist.h_passed = [])) && Decider.valid (smk_impl (inv, f))) in
    result

(* Returns true if the candidate loop invariant is new and runs
   using strongest_postcondition with no problems. *)
let sp_check_candidate
    (env : inference_env_t)
    (hist : history_t) 
    (f : form) : bool =
  incr_check_count ();
  let failed = poor_candidate hist f || 
    not (try_executing_sp env hist (smk_and (f :: hist.h_passed))) in
  let resstr = if failed then "FAILED" else "PASSED" in
    if (failed) then
      hist.h_failed <- f :: hist.h_failed
    else
      hist.h_passed <- f :: hist.h_passed;
    print_string ("\n" ^ resstr ^ " [" ^ (string_of_int !check_count) ^ 
		    "] " ^ (PrintForm.string_of_form f) ^ "\n");
    not failed

let rec check_interpreted
    (inv_checker : (form -> bool)) 
    (to_check : form list)
    (checked : form list) : form list * bool =
    match to_check with
      | [] -> checked, false
      | f :: fs ->
	  let checked = checked @ [f] in
	  let res = inv_checker (smk_and checked) in
	    if res then (checked, true)
	    else check_interpreted inv_checker fs checked

let interpret_candidates 
    (hist : history_t) 
    (env : inference_env_t)
    (inv_checker : (form -> bool))
    (fs : form list) : bool =
  let fs, fs' = List.partition (fun x -> (not (trivial x))) fs in
    hist.h_failed <- hist.h_failed @ fs';
    not (fs = []) &&
      (print_results ((string_of_int (List.length fs)) ^ " CANDIDATES") fs;
       match Util.split_by "." !CmdLine.driver_method with
	 | [class_name; proc_name] ->
	     let im = AstUtil.must_find_im class_name env.ie_program in
	     let proco = AstUtil.find_proc proc_name im in
	       (match proco with
		  | Some proc ->
		      let passed = Interpreter.test_invariants 
			env.ie_program im proc (fs, hist.h_loop) in
		      let passed = List.sort order_by_depth passed in
			if passed = [] then false
			else
			  let passed, result = check_interpreted inv_checker 
			    passed hist.h_passed in
			  let failed = List.filter 
			    (fun x -> not (List.mem x passed)) fs in
			    hist.h_passed <- passed;
			    hist.h_failed <- hist.h_failed @ failed;
			    result
		  | None -> 
		      let err = ("interpret_candidates: procedure " ^ 
				   !CmdLine.driver_method ^ " not found") in
			raise (InferenceFailure err))
	 | _ -> 
	     let err = ("interpret_candidates: implementation module not " ^ 
			  "found for " ^ !CmdLine.driver_method) in
	       raise (InferenceFailure err))

let filter_bound_exprs (fs : form list) (e : expr_t) : form list =
  match e with
    | FreeExpr f -> fs @ [f]
    | _ -> fs

(* Make substitution maps where the given variable identifier is
   replaced by other expressions in its equivalence class. *)
let make_var_substMaps 
    (ecs : equiv_classes_t) 
    (filter_function : form -> bool)
    (to_subst : ident) : substMap list =
  let exprs = get_equivalent ecs (FreeExpr (Var to_subst)) in
  let fs = List.fold_left filter_bound_exprs [] exprs in
  let fs = List.filter filter_function fs  in
    List.map (fun f -> [(to_subst, f)]) fs

(* Make substitution maps where the given constant value is replaced
   by other expressions in its equivalence class. *)
let make_const_substMaps
    (ecs : equiv_classes_t) 
    (filter_function : form -> bool)
    (to_subst : constValue) : cSubstMap list =
  let exprs = get_equivalent ecs (FreeExpr (Const to_subst)) in
  let fs = List.fold_left filter_bound_exprs [] exprs in
  let fs = List.filter filter_function fs in
    List.map (fun f -> [(to_subst, f)]) fs

let return_true (f : form) : bool = true

(* Replaces variables in the given formulas with expressions from the
   corresponding equivalence class. *)
let simple_replacement 
    (ecs : equiv_classes_t) (template : form) : form list =
  let make_vsms = make_var_substMaps ecs return_true in
  let make_csms = make_const_substMaps ecs return_true in
  let rmsv = List.flatten (List.map make_vsms (fv template)) in
  let fsv = List.map (fun (rm) -> clean_up (subst rm template)) rmsv in
  let rmsc = List.flatten (List.map make_csms (get_consts template)) in
  let fsc = List.map (fun (rm) -> clean_up (subst_const rm template)) rmsc in
    Util.remove_dups (fsv @ fsc)

(* Replaces variables in the given formulas with other variables or
   constants.  Avoid substituting with expressions so as to limit the
   depth of resulting formulas. *)
let smart_replacement 
    (ecs : equiv_classes_t) (template : form) : expr_t list =
  let make_vsms = make_var_substMaps ecs is_simple_expr in
  let make_csms = make_const_substMaps ecs is_simple_expr in
  let rmsv = List.flatten (List.map make_vsms (fv template)) in
  let fsv = List.map (fun (rm) -> clean_up (subst rm template)) rmsv in
  let rmsc = List.flatten (List.map make_csms (get_consts template)) in
  let fsc = List.map (fun (rm) -> clean_up (subst_const rm template)) rmsc in
  let fs = List.filter not_constant (Util.remove_dups (fsc @ fsv)) in
    List.map mk_freeExpr fs

let iterate_expr (ecs : equiv_classes_t) (e : expr_t) : equiv_classes_t =
  match e with
    | BoundExpr _ -> ecs
    | FreeExpr f ->
	if (is_simple_expr f) then ecs
	else
	  let nfs = smart_replacement ecs f in
	  let ec0, ecs0 = get_equiv_class e ecs in
	  let ec1, ecs1 = 
	    List.fold_left add_to_equiv_class (ec0, ecs0) nfs in
	    ec1 :: ecs1

let rec drop_one_lists 
    (acc : 'a list list) (hd : 'a list) (tl : 'a list) : 'a list list =
  match tl with
    | f :: fs -> 
	drop_one_lists (acc @ [hd @ fs]) (hd @ [f]) fs
    | [] -> acc

let rec strengthen_formula (t : form) : form list =
  match t with
    | Binder(b, til, t0) ->
	let fs = strengthen_formula t0 in
	  List.map (fun x -> Binder(b, til, x)) fs
    | App(Const Impl, [f0; f1]) ->
	let fs0 = weaken_formula f0 in
	let fs1 = strengthen_formula f1 in
	  (List.map (fun x -> smk_impl (x, f1)) fs0) @
	    (List.map (fun x -> smk_impl (f0, x)) fs1)
    | _ -> [t]
and weaken_formula (t : form) : form list =
  match t with
    | App(Const And, fs) ->
	List.map smk_and (drop_one_lists [] [] fs)
    | _ -> [t]

let instantiate_template (ecs : equiv_classes_t) (t : form) : form list =
  match t with
    | Binder(Forall, (id, _) :: til, f0) ->
	let exprs = get_equivalent ecs (BoundExpr (Var id, [])) in
	let fs = List.fold_left filter_bound_exprs [] exprs in
	  List.map (fun x -> subst [(id, x)] f0) fs
    | _ -> []

let get_subst 
    (ecs : equiv_classes_t) 
    (sc : typedIdent list) 
    (t : form) : form list =
  let exprs, _ = get_equiv_class (expr_of_form sc t) ecs in
  let fs = List.fold_left
    (fun x y ->
       match y with
	 | FreeExpr f -> x @ [f]
	 | BoundExpr (f, til) ->
	     if (List.for_all (fun z -> List.mem z sc) til) then
	       x @ [f]
	     else x) [] exprs in
    Util.remove_dups (List.map clean_up fs)

let rec subst_one_expr
    (ecs : equiv_classes_t) 
    (sc : typedIdent list) 
    (t : form) : form list =
  let fs0 = get_subst ecs sc t in
  let fs1 =
    match t with
      | TypedForm(f, tf) ->
	  List.map (fun x -> TypedForm(x, tf)) (subst_one_expr ecs sc f)
      | Binder(b, til, f) ->
	  List.map 
	    (fun x -> Binder(b, til, x))
	    (subst_one_expr ecs (current_scope sc til) f)
      | App(f, fs) ->
	  let l_f = subst_one_expr ecs sc f in
	  let fs0 = List.map (fun x -> App(x, fs)) l_f in
	  let l_fs = List.map (subst_one_expr ecs sc) fs in
	  let rec mk_args 
	      (l_fs : form list list)
	      (hd : form list) 
	      (tl : form list) : form list list = 
	    match l_fs, tl with
	      | l_f :: l_fs', x :: tl' ->
		  (List.map (fun y -> hd @ (y :: tl')) l_f) @
		    (mk_args l_fs' (hd @ [x]) tl')
	      | [], [] -> []
	      | _ -> failwith "subst_one_expr can't happen" in
	  let fs1 = List.map (fun x -> App(f, x)) (mk_args l_fs [] fs) in
	    fs0 @ fs1
      | _ -> [] in
    Util.remove_dups (List.map clean_up (fs0 @ fs1))

let heuristically_generate 
    (ecs : equiv_classes_t) (ts : form list) : form list =
  List.flatten (List.map (instantiate_template ecs) ts)
      
(* Make one pass at generating more complex expressions in the
   equivalence classes. *)
let iterate_exprs (ecs : equiv_classes_t) : equiv_classes_t =
  List.fold_left iterate_expr ecs (List.flatten ecs)

let candidates_of_template 
    (ecs : equiv_classes_t) 
    (acc : form list) 
    (template : form) : form list =
  Util.union (simple_replacement ecs template) acc

let filter_candidates 
    (env : inference_env_t) 
    (candidates : form list) : form list =
  let candidates = List.filter non_tmp_only candidates in
  let candidates = List.filter no_ref_to_result candidates in
  let candidates = 
    List.filter (no_ref_to_non_fvs env.ie_fvs) candidates in
  let candidates = List.filter no_field_writes candidates in
  let candidates = List.filter (not_type_check env) candidates in
  let candidates = List.filter not_alloc_check candidates in
    candidates  

let generate_candidates 
    (env : inference_env_t)
    (hist : history_t)
    (ecs : equiv_classes_t) 
    (templates : form list) : form list =
  let candidates = 
    List.fold_left (candidates_of_template ecs) [] templates in
  let candidates = Util.difference candidates hist.h_passed in
  let candidates = Util.difference candidates hist.h_failed in
    filter_candidates env candidates

(* Mostly copied from Analyze to avoid circular dependencies between
   modules.  A bad idea, but Viktor made me do it. *)
let process_obligations 
    (name : string)
    (obs : obligation list) : bool =
  let _ = Decider.start name in
  let _ = Util.msg (Printf.sprintf "Generated %d proof obligations.\n"
		      (List.length obs)) in
  let p_oblig (ob : obligation) : bool =
    let obstr = 
      (if !Util.verbose then string_of_oblig ob
       else short_string_of_oblig ob) in
    let obname = name_of_oblig ob in
    let _ = debug_lmsg 0 (fun () -> "\nVERIFICATION CONDITION:\n" ^ obstr ^"\n") in
    let res = Decider.ob_valid ob true in
      if res then debug_lmsg 0 (fun () -> "\nVERIFICATION CONDITION " ^ 
				  obname ^ " is VALID.\n")
      else debug_lmsg 0 (fun () -> ("\nVERIFICATION CONDITION " ^ obname ^ " is INVALID.\n"));
      res in
  let res = List.for_all p_oblig obs in
  let count_method = Str.string_match (Str.regexp (Str.quote "_INIT")) name ((String.length name) - 5) in
    (Decider.stop count_method; res)

let check_candidates
    (hist : history_t)
    (form_checker : (form -> bool))
    (inv_checker : (form -> bool))
    (candidates : form list) : bool =
  let rec check_candidates_rec (candidates : form list) : bool =
    match candidates with
      | [] -> false
      | c0 :: cs0 ->
	  let result = form_checker c0 in
	    if result && inv_checker (smk_and hist.h_passed) then true
	    else check_candidates_rec cs0 in
  let candidates = List.sort order_by_depth candidates in
  let n = string_of_int (List.length candidates) in
  let _ = print_string ("Checking " ^ n ^ " candidates\n") in
  let _ = print_results "CANDIDATES" candidates in
    clear_check_count ();
    check_candidates_rec candidates

let check_invariant 
    (env : inference_env_t) 
    (hist : history_t) 
    (inv : form) : bool =
  print_string 
    ("Checking invariant:\n" ^ (PrintForm.string_of_form inv) ^ "\n");
  let old_inv = hist.h_loop.loop_inv in (* save invariant *)
    hist.h_loop.loop_inv <- Some inv;
    let obs = Vcgen.vcs_of_procedure env.ie_program env.ie_impl
      env.ie_proc env.ie_phdr env.ie_conc true in
    let result = process_obligations env.ie_phdr.p_name obs in
      hist.h_loop.loop_inv <- old_inv; (* restore *)
      result
	    
(* Iterate equivalence classes until timeout. *)
let iterate_until
    (env : inference_env_t)
    (hist : history_t)
    (templates : form list) 
    (ecs : equiv_classes_t) : equiv_classes_t =
  let form_checker = sp_check_candidate env hist in
  let inv_checker = check_invariant env hist in
  let check_all = if !CmdLine.interpret then
    interpret_candidates hist env inv_checker
  else check_candidates hist form_checker inv_checker in
  let rec iterate_until_rec (ecs : equiv_classes_t) : equiv_classes_t =
    if (Unix.time () > env.ie_timeout) then ecs
    else 
      let ecs = iterate_exprs ecs in
      let candidates = generate_candidates env hist ecs templates in
	print_equiv_classes ecs;
	if candidates = [] then ecs
	else
	  (let result = check_all candidates in
	     print_results "PASSED" hist.h_passed;
	     if result then ecs (* stop if verifies *)
	     else iterate_until_rec ecs) in
  let result = check_all (filter_candidates env templates) in 
    (* First check the templates *)
    print_results "PASSED" hist.h_passed;
    if result then ecs
    else (* Next use heuristics *)
      let candidates = heuristically_generate ecs templates in
      let result = check_all candidates in
	print_results "PASSED" hist.h_passed;
	if result then ecs
    else (* Next try a simple substitution *)
      let candidates = generate_candidates env hist ecs templates in
      let result = check_all candidates in
	print_results "PASSED" hist.h_passed;
	if result then ecs
	else iterate_until_rec ecs

let iterate_with_new_templates
    (env : inference_env_t)
    (hist : history_t)
    (templates : form list) 
    (ecs : equiv_classes_t) : form list =
  let form_checker = sp_check_candidate env hist in
  let inv_checker = check_invariant env hist in
  let check_all = if !CmdLine.interpret then
    interpret_candidates hist env inv_checker
  else check_candidates hist form_checker inv_checker in
  let rec iterate_with_new_rec (t : form list) : form list =
    if (Unix.time () > env.ie_timeout) then t
    else 
      let candidates = generate_candidates env hist ecs t in
	if candidates = [] then t
	else
	  let result = check_all candidates in
	  let _ = print_results "PASSED" hist.h_passed in
	    if result then t
	    else iterate_with_new_rec (Util.union t candidates) in
  let candidates =
    Util.union templates (heuristically_generate ecs templates) in
  let result = check_all (filter_candidates env candidates) in 
    (* First check the templates *)
    print_results "PASSED" hist.h_passed;
    if result then candidates
    else iterate_with_new_rec candidates

let minimize_invariant 
    (env : inference_env_t) (hist : history_t) : form list =
  let rec minimize_until (fs : form list) : form list =
    let fs0 = minimize_invariant_rec [] fs in
      if (List.length fs0) < (List.length fs) then
	minimize_until fs0
      else fs0
  and minimize_invariant_rec 
	(checked : form list) (to_check : form list) : form list =
      match to_check with
	| f0 :: fs0 ->
	    let fs1 = checked @ fs0 in
	    if fs1 <> [] && check_invariant env hist (smk_and fs1) then
	      minimize_invariant_rec checked fs0
	    else minimize_invariant_rec (checked @ [f0]) fs0
	| [] -> checked in
    minimize_until hist.h_passed

let compute_fvs
    (proc : proc_def)
    (svds : specvar_def list)
    (prec : form)
    (post : form) : ident list =
  let fvs = fvs_of_cmd proc.p_body in
  let fvs = List.fold_left fvs_of_vd fvs svds in
  let fvs = fvs_of_form fvs prec in
  let fvs = fvs_of_form fvs post in
  let msg = List.fold_left (fun x y -> x ^ " " ^ y) "FVS: " fvs in
    print_string (msg ^ "\n");
    fvs

let infer_loop_invariants
    (prog : program)
    (impl : impl_module)
    (proc : proc_def)
    (phdr : proc_header)
    (conc : specvar_def list) (* concretization *) : unit =
  let _ = debug_msg ((PrintAst.pr_command proc.p_body) ^ "\n") in
  let stop_time = Unix.time () +. (float_of_int !CmdLine.inferTimeOut) in
  (* Here we do the work that is common to the entire procedure. *)
  let sm = AstUtil.must_find_sm impl.im_name prog in
  let mapping = List.find (fun m -> m.map_impl = impl) prog.p_maps in
  let precond = Sast.concretized_pre prog impl phdr in
  let pre_conjuncts = FormUtil.get_conjuncts precond in
  let postcond = Sast.concretized_post prog impl proc phdr proc.p_body in
  let post_conjuncts = FormUtil.get_conjuncts postcond in
  let spec_inv = List.map (fun x -> x.Specs.inv_form) (sm.sm_free_invs @ sm.sm_invs) in
  let impl_inv = List.map (fun x -> x.Specs.inv_form) impl.im_invs in
  let conjuncts = Util.union pre_conjuncts post_conjuncts in
  let templates = Util.union conjuncts (get_templates proc) in
  let _ = print_results "PRECOND CONJUNCTS" pre_conjuncts in
  let _ = print_results "POSTCOND CONJUNCTS" post_conjuncts in
  let _ = print_results "SPEC INVS" spec_inv in
  let _ = print_results "IMPL INVS" impl_inv in
  let _ = print_results "TEMPLATES" templates in
  let ids_to_old = AstUtil.get_variables_to_old proc.p_body in
  let old_fs = List.map make_eq_to_old ids_to_old in
  let precond_and_old = smk_and (precond :: old_fs) in
  let vds = proc.p_vardefs @ impl.im_vardefs @ impl.im_constdefs @
    sm.sm_vardefs @ sm.sm_constdefs @ mapping.map_abst in
  let _ = print_results "PRECOND WITH OLD" [precond_and_old] in
  let ecs = basic_equivalence proc.p_body conjuncts vds in
  (* Incorporate context information into equivalence classes *)
  let fs = 
    (reduce_to_formulas proc.p_body) @ conjuncts @ (form_of_svs vds) in
  let cm = Hashtbl.create 100 in
  let _ = List.iter (collect_contexts [] cm) fs in
  let ecs = incorporate_context ecs cm in
  let _ = print_equiv_classes ecs in
  let _ = print_string ("ACCESSIBLE\n") in
  let _ = List.iter 
    (fun x -> (print_string ((PrintAst.pr_var_decl x) ^ "\n"))) 
    (AstUtil.accessible_specvars prog impl.im_name) in
  let _ = print_string ("VARDEFS\n") in
  let _ = print_string (PrintAst.pr_vardefs proc.p_vardefs ^ "\n ***** ") in
  let _ = print_string (PrintAst.pr_vardefs impl.im_vardefs ^ "\n ***** ") in
  let _ = print_string (PrintAst.pr_vardefs impl.im_constdefs ^ "\n ***** ") in
  let _ = print_string (PrintAst.pr_vardefs sm.sm_vardefs ^ "\n ***** ") in
  let _ = print_string (PrintAst.pr_vardefs sm.sm_constdefs ^ "\n ***** ") in
  let _ = print_string (PrintAst.pr_vardefs mapping.map_abst ^ "\n ***** ") in
  let env = 
    { ie_program = prog;
      ie_impl = impl;
      ie_proc = proc;
      ie_phdr = phdr;
      ie_conc = conc;
      ie_precondition = precond_and_old;
      ie_iterations = loop_iterations;
      ie_classes = List.map (fun x -> x.im_name) prog.p_impls;
      ie_fvs = compute_fvs proc vds precond postcond;
      ie_timeout = stop_time; } in
  let infer (lc : loop_command) (outer_loops : command list) : unit =
    print_string ("\nINFERRING FOR:\n" ^ (PrintAst.pr_command (Loop lc)) ^ "\n\n");
    let hist = {h_passed = []; h_failed = []; h_loop = lc;} in
    let templates = List.map clean_up templates in
    let _ = iterate_with_new_templates env hist templates ecs in
    let result = if !CmdLine.inferMinimize 
    then minimize_invariant env hist else hist.h_passed in
      lc.loop_inv <- Some (smk_and result);
      print_results "INFERRED LOOP INVARIANT" result;
      flush_all () in
    handle_next_loop infer [] proc.p_body
