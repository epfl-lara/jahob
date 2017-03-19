(* Interface to MONA. *)

let infile = ref (Util.tmp_name "in.mona")
let mona_name = "mona"
let valid_formula = "Formula is valid"
let invalid_formula = "Formula is unsatisfiable"
let counter_example = "A counter-example"
let out_of_memory="*** out of memory, execution aborted ***"

open Util
open MonaForm
open MonaConvert
open MonaPrint
open Common

(* debug messages *)

let debug_id = Debug.register_debug_module "Mona"
let debug_msg = Debug.debug_msg debug_id
let debug_lmsg = Debug.debug_lmsg debug_id

(* default options *)

let default_opts () : options_t = 
  let mona_defaults = [("TimeOut",       string_of_int !CmdLine.timeout);
		       ("QuantInst",  "no");
		       ("KeepSpecVars", "yes")] 
  in map_of_list mona_defaults

let make_new_infile () : unit =
  infile := Util.tmp_name "in.mona"

(* change by Alexander Malkis: *)
(* Remove the initial empty lines from the channel and try to output the first nonempty line; then close the channel. Raise End_of_file if there are no lines at all. If there are only empty lines, return the empty line. *)
let fileToLine chn =
  let rec fileToLine_aux () =
    try 
      let str = input_line chn in
      if ((String.length str)=0) then fileToLine_aux () 
      else (close_in chn; str)
    with End_of_file -> close_in chn; ""
  in
    try
      let str = input_line chn in
      if ((String.length str)=0) then fileToLine_aux ()
      else (close_in chn; str)
    with End_of_file -> close_in chn; raise End_of_file

type lineParseResult = Nothing | ParsedLine of string      
    
let parse_line s = 
  if String.contains s '=' then ParsedLine s
  else Nothing
      
let parse_counterexample fn = 
  let chn = open_in fn in
  try
    let firstLine = input_line chn in
    let expectedStr = "A counter-example of least length" in
    let leftContains str substr = 
      try (String.sub str 0 (String.length substr) = substr) with
	Invalid_argument _ -> false in
    let res = ref "\nFailed to retrieve a counterexample.\n" in
    let line = ref "" in
    if leftContains firstLine expectedStr then begin
      try begin        
	while (parse_line !line = Nothing) do
          line := input_line chn
	done;
	res := !line ^ "\n";
	while (parse_line !line <> Nothing) do
          (match (parse_line !line) with
            ParsedLine s -> res := !res ^ s ^ ", "
          | Nothing -> fail "Mona.parseCounterexample: BUG");
          line := input_line chn
	done;
	res := !res ^ "\n"
      end with End_of_file -> ()
    end else ();
    close_in chn;
    !res
  with e -> close_in chn; raise e

(* [parse_output_valid str]  
   returns [Some true], if the argument indicates that MONA has proven the validity,
   returns [Some false], if the argument indicates that MONA has proven that the formula is invalid,
   returns [None], if the argument indicates that MONA has run out of memory, and
   fails otherwise.
   Changed by AM.
*)
let parse_output_valid str =
  if str = valid_formula then Some true
  else if str = invalid_formula then Some false (* Changed by AM. Previously: None, with a comment: "keep track of formula abstractions and replace with Some false if possible" *)
  else if (try (String.sub str 0 (String.length counter_example) = counter_example) with
      Invalid_argument _ -> false) then Some false (* Changed by AM. Previously: None *)
  else if str = out_of_memory then None
  else begin
    make_new_infile ();
    fail ("Error when calling MONA: " ^ str)
  end  

let run_mona timeout prog =
  let chn = open_out !infile in
  let _ = print_prog chn prog; close_out chn in
  let _, in_chan = run_with_timeout_redirect_out
      mona_name ["-q"; !infile] timeout false
  in in_chan

(* Tries to prove f via MONA. 
   Returns Some true if MONA proved f. 
   Returns Some false if MONA was able to show that f is invalid.
   Returns None if MONA went out of resources. Fails in all other cases.
*)
let mona_valid =
  let regexp = Str.regexp "counter-example of least length (\\([0-9]+\\))" in
  let match_size s = 
    try ignore (Str.search_forward regexp s 0); true with Not_found -> false
  in 
  fun timeout mode preamble f ->
    debug_lmsg 4 (fun () -> "Running MONA executable...\n");
    let in_chan = run_mona timeout (mode, preamble@[FormDecl f]) in 
    debug_lmsg 4 (fun () -> "MONA terminated, parsing output...");
    let result_string = fileToLine in_chan in
    let res = parse_output_valid result_string in
    debug_lmsg 4 (fun () -> "Parsed MONA output.\n");
    (match res with 
        Some false -> 
          if match_size result_string
          then debug_msg ("size of counter-model: " ^ 
                             Str.matched_group 1 result_string ^ "\n")
	  else ()
      | _ -> ());
    res

(* returns Some true if the formula was shown to be valid, 
   returns Some false if the formula was shown to be invalid, 
   returns None if nothing could be found out about the validity,
   and fails otherwise.
   We could return Some false instead of None in more cases, namely when conversion into the input language of MONA was precise. However, approximations are possible, i.e. valid formulas could be converted into invalid ones. Future work: tracking whether approximations have happened or not.
*)
let valid env derived bb_fields field_types options f =
  let timeout = int_of_string (get_option options "TimeOut") in
    debug_lmsg 4 (fun () -> "Converting MONA formula...");
    let mode, preamble, f' = convert env derived bb_fields field_types f in
    match f' with
      |	Atom True -> Some true
      |	Atom False -> None 
      |	_ -> (let res=mona_valid timeout mode preamble f' in
	       (match res with
                   Some false -> None
                 | _ -> res
               )
             )

open Form
open FormUtil

let extract_field_types fs =
  let rec extract acc = function
    | [] -> acc
    | f::fs' -> (match strip_types f with
      |	App (Var "pointsto", [domain; Var fld; range])
      |	App (Const Comment, [_; App (Var "pointsto", [domain; Var fld; range])]) ->
	  extract ((fld, (domain, range)) :: acc) fs'
      |	_ -> extract acc fs')
  in extract [] fs

(*
let rec compact_binders = function
  | App (f, fs) ->
      App (compact_binders f, List.map compact_binders fs)
  | TypedForm (f, ty) -> TypedForm (compact_binders f, ty)
  | Binder (Lambda as b, vts1, Binder (Lambda, vts2, f))
  | Binder (Exists as b, vts1, Binder (Exists, vts2, f))
  | Binder (Forall as b, vts1, Binder (Forall, vts2, f)) ->
      compact_binders (Binder (b, vts1 @ vts2, f))
  | Binder (b, vts, f) -> Binder (b, vts, compact_binders f)
  | f -> f
*)

let instantiate_quantifiers env derived_fields (fs0, g) =
  let _, sub = elim_free_vars false [] (fs0, g) in
  let fs = List.fold_left (fun acc -> function 
    | Binder (Forall, vts, f) when not (Util.disjoint derived_fields (fv (subst sub f))) ->
	(vts, f) :: acc
    | _ -> acc) [] fs0
  in
  let instantiate (vts, f) =
    let is_unifiable_var v = List.exists (fun (v', _) -> v = v') sub in
    let fv_f = Util.union (List.rev_map fst vts) (List.filter is_unifiable_var (fv f)) in
    let rec subterms acc = function
      |	[] -> acc
      |	TypedForm (f, _) :: fs -> subterms acc (f :: fs)
      |	(App (Var _, [Var v]) as f) :: fs
      |	(App (TypedForm (Var _, _), [TypedForm (Var v, _)]) as f) :: fs
      |	(App (Const FieldRead, [TypedForm (Var _, _); TypedForm (Var v, _)]) as f) :: fs 
      |	(App (Const FieldRead, [Var _; Var v]) as f) :: fs ->
	  subterms ((f, Util.union [v] fv_f) :: acc) fs
      |	App (_, fs') :: fs -> subterms acc (List.rev_append fs' fs)
      |	_ :: fs -> subterms acc fs
    in
    let _ = print_endline "\nform:"; PrintForm.print_form f in
    let candidates = subterms [(g, Util.union (List.filter is_unifiable_var (fv g)) fv_f)] [g] in
    let _ = print_endline "candidates:"; List.iter (fun (g, _) -> PrintForm.print_form g) candidates in 
    let _ = print_endline "instantiations:" in
    let rec match_rhs = function
      |	Var _ :: fs 
      |	TypedForm (Var _, _) :: fs -> match_rhs fs
      |	f :: fs ->
	  let unifiable, mgu = List.fold_left (fun (unifiable, mgu) (g, unifiable_vs) ->
	    if unifiable then unifiable, mgu else
	    is_unifiable [] unifiable_vs g f) (false, []) candidates
	  in
	  if unifiable then unifiable, mgu else
	  (match f with
	  | App (_, fs') -> match_rhs (List.rev_append fs' fs)
	  | _ -> match_rhs fs)
      |	[] -> false, []	  
    in
    let matched, mgu = match_rhs [f] in
    if not matched then [] else
    let sub, vts' = 
      List.fold_left (fun (sub, vts') (v, _ as vt) ->
	try (v, List.assoc v mgu) :: sub, vts'
	with Not_found -> sub, vt :: vts') ([], []) vts
    in
    if sub = [] then [] else
    let f' = smk_foralls (vts', subst sub f) in
    if TypeReconstruct.well_typed env f' then
      let _ = PrintForm.print_form f' in [f'] else []
  in
  let new_fs = List.fold_left (fun acc (vts, f) -> instantiate (vts, f) @ acc) [] fs in
  (List.rev_append new_fs fs0, g)

(*
let instantiate_quantifiers env derived_fields (fs0, g) =
  let _, sub = elim_free_vars false [] (fs0, g) in
  let fs = List.fold_left (fun acc -> function 
    | Binder (Forall, vts, f) when not (Util.disjoint derived_fields (fv (subst sub f))) ->
	(vts, f) :: acc
    | _ -> acc) [] fs0
  in
  let rec collect vs =
    let vs' = List.fold_left 
	(fun vs f ->
	  let fv_f = fv f in
	  if List.exists (fun v -> List.mem v vs) fv_f then
	    Util.union fv_f vs
	  else vs) vs fs0
    in if Util.difference vs' vs = [] then vs else collect vs'
  in 
  let inst_vs = List.filter (fun v -> List.assoc v env = mk_object_type) (collect (fv g)) in
  let rec instantiate acc = function 
    | ((v, ty) :: vts, f) :: fs when ty = mk_object_type ->
	let fs_inst = List.rev_map (fun inst_v -> (vts, subst [(v, mk_var inst_v)] f)) inst_vs in
	instantiate acc (List.rev_append fs_inst fs)
    | (vts, f) :: fs ->
	let f_inst = smk_foralls (vts, f) in
	instantiate (f_inst :: acc) fs
    | [] -> acc
  in 
  (instantiate fs0 fs, g)
  *)

let mk_parent_fc = 
  let xs, ys, zs = fresh_name "v", fresh_name "v", fresh_name "v" in
  let x, y, z = mk_var xs, mk_var ys, mk_var zs in
  fun parent (bb_fields : Form.form list) ->
    let p = Var parent in
    let bb z x = mk_or (List.map (fun f -> mk_eq (App (f, [z]), x)) bb_fields) in
    let has_parent1 = mk_neq (x, mk_null) in
    let has_parent2 = 
      mk_exists (zs, mk_object_type, bb z x)
    in
    let has_parent = mk_and [has_parent1; has_parent2] in
    let parent_def = 
      mk_foralls ([(xs, mk_object_type); (ys, mk_object_type)],
		  mk_impl (mk_eq (App (p, [x]), y), 
			   mk_and [mk_impl (has_parent, bb y x);
				   mk_impl (mk_not has_parent, mk_eq (y, mk_null))]))
    in 
    (parent, (parent_def, false))

(* Tries to prove a sequent. Returns Some true if f was shown valid.
   Returns Some false if f was shown invalid.
   Returns None if nothing was found out, either due to MONA running out of resources, or due to imprecision of the translation.
   Fails in all other cases.
*)
let prove_sequent (options : options_t) env (fs0, g0) =
  let options = merge_opts (default_opts ()) options in
  let (fs,g) = (List.map remove_comments fs0, remove_comments g0) in
  (* let env = fv (mk_impl (mk_and fs, g)) in *)
  let _ = debug_lmsg 4 (fun () -> "Mona proving sequent:\n" ^ string_of_sequent (fs,g) ^ "\n") in
  let add_tree_decl bb_fields tree_decls =
    let rec merge acc tree_decls = match tree_decls with
      |	[] -> bb_fields :: acc
      |	bb_fields' :: tree_decls' ->
	  if empty (difference bb_fields bb_fields') then List.rev_append tree_decls acc
	  else if empty (difference bb_fields' bb_fields) then List.rev_append (bb_fields::tree_decls') acc 
	  else merge (bb_fields' :: acc) tree_decls'
    in merge [] tree_decls
  in
  let field_types = extract_field_types fs in
  let get_arg_type fld = 
    try fst (List.assoc fld field_types)
    with Not_found -> mk_var "Object"
  in
  let disjoint =
    let disjoint_classes = List.fold_left (fun acc f ->
      match strip_types f with
      |	App (Const Eq, [App (Const Cap, [c1; c2]); App (Const FiniteSetConst, [Const NullConst])])
      |	App (Const Comment, [_; App (Const Eq, [App (Const Cap, [c1; c2]); App (Const FiniteSetConst, [Const NullConst])])]) ->
	  (c1, c2) :: acc
      |	_ -> acc) [] fs
    in
    fun c1 c2 -> 
      c1 <> c2 && 
      (List.mem (c1, c2) disjoint_classes || 
      List.mem (c2, c1) disjoint_classes)
  in
  let pairwise_disjoint fld flds =
    List.for_all (fun fld' -> disjoint (get_arg_type fld) (get_arg_type fld')) flds
  in
  let optimize_rep tree_decl =
    let rec merge_field acc fld_classes fld = 
      match fld_classes with
      |	[] -> [fld]::acc
      |	fldc :: fld_classes1 ->
	  if pairwise_disjoint fld fldc then
	    (fld :: fldc) :: acc @ fld_classes1
	  else merge_field (fldc :: acc) fld_classes1 fld
    in
    List.fold_left (merge_field []) [] tree_decl
  in
  let has_field_type fld = 
    let is_object_type ty = match ty with
    | TypeApp (TypeObject, []) -> true
    | _ -> false
    in
    try match List.assoc fld env with
    | TypeApp (TypeArray, [ty1; ty2]) 
    | TypeFun ([ty1], ty2)
      -> is_object_type ty1 && is_object_type ty2
    | _ -> false
    with Not_found -> false 
  in
  let fail msg = raise (Invalid_argument msg) in
  try
    let _ = debug_lmsg 4 (fun () -> "sequent after elimination of free variables:\n" ^ string_of_sequent (fs,g) ^ "\n") in
    (* get field constraints and backbone fields from antecedent *)
    let fcs, tree_decls, fs' = List.fold_left (fun (fcs, tree_decls, fs') f ->
      match normalize 4 f with
      (* match non-deterministic field constraints *)
      | Binder (Forall, [(x1, _); (y1, _)], App(Const Impl, [App (Const Eq, [App (Const FieldRead, [Var fld; Var x2]); Var y2]); fld_def]))
      | Binder (Forall, [(x1, _); (y1, _)], App(Const Impl, [App (Const Eq, [App (Var fld, [Var x2]); Var y2]); fld_def]))
	when x1 = x2 && y1 = y2 ->
	  if has_field_type fld then ((fld, (f, false)) :: fcs, tree_decls, fs')
	  else (fcs, tree_decls, f::fs')
      (* match deterministic field constraints *)
      | Binder (Forall, [(x1, _); (y1, _)], App(Const Iff, [App (Const Eq, [App (Const FieldRead, [Var fld; Var x2]); Var y2]); fld_def]))
      | Binder (Forall, [(x1, _); (y1, _)], App(Const Iff, [App (Const Eq, [App (Var fld, [Var x2]); Var y2]); fld_def]))
	when x1 = x2 && y1 = y2 ->
	  if has_field_type fld then ((fld, (f, true)) :: fcs, tree_decls, fs')
	  else (fcs, tree_decls, f::fs')
      (* match backbone fields *)
      | App (Var vtree, [App (Const ListLiteral, fields)]) when vtree = str_tree -> 
	  let bb_fields = List.fold_left (fun bb_fields -> 
	    function | (Var fld) -> 
	      if has_field_type fld then fld :: bb_fields
	      else fail (Printf.sprintf "Tried to declare a backbone field which is not of type field:\n    %s :: %s." 
			   fld (PrintForm.string_of_type (try List.assoc fld env with Not_found -> TypeUniverse)))
	  | _ -> fail "Only atomic backbone fields supported.") [] fields 
	  in 
	  let tree_decls' = add_tree_decl bb_fields tree_decls in
	  (fcs, tree_decls', fs')
      | App (Var vtree, [Var parent; App (Const ListLiteral, fields)]) when vtree = str_ptree -> 
	  let bb_fields = List.fold_left (fun bb_fields -> 
	    function | (Var fld) -> 
	      if has_field_type fld then fld :: bb_fields
	      else fail (Printf.sprintf "Tried to declare a backbone field which is not of type field:\n    %s :: %s." 
			   fld (PrintForm.string_of_type (try List.assoc fld env with Not_found -> TypeUniverse)))
	  | _ -> fail "Only atomic backbone fields supported.") [] fields 
	  in 
	  let tree_decls' = add_tree_decl bb_fields tree_decls in
	  let fcs' = mk_parent_fc parent fields :: fcs in 
	  (fcs', tree_decls', fs')
      | _ -> (fcs, tree_decls, f :: fs')) ([], [[]], []) fs
    in
    let bb_fields = match tree_decls with
    | [bb_fields] -> bb_fields
    | bb_fields::_ -> 
	Util.msg "Found multiple tree declarations in antecedent, using the last one.";
	(* We could instead check which one intersects more free variables.
	   Currently we take the last one, which is usually what we want. *)
	bb_fields
    |  _ -> (Util.msg "moep"; [])
    in
    let _ = debug_lmsg 4 (fun () -> "Generating missing field constraints...") in
    (* generate missing field constraints *)
    let (trivial_fc : (string list) ref) = ref [] in
    let fcs', unconstr_fields = 
      let x = "x" and y = "y" in
      List.fold_left (fun (fcs', unconstr_fields) (v, ty) ->
	if has_field_type v then
	  let is_derived = List.exists (fun (v', _) -> v' = v) fcs'
	  and is_backbone = List.mem v bb_fields in
	  if not (is_derived || is_backbone) then
	    let _ = (trivial_fc := v :: !trivial_fc) in
	    let fc = Binder (Forall, [(x, mk_object_type); (y, mk_object_type)], 
			     App(Const Impl, [App (Const Eq, [App (Var v, [Var x]); Var y]); mk_true]))
	    in 
	      (v, (fc, false)) :: fcs', v :: unconstr_fields 
	  else if is_derived && is_backbone then
	    fail ("Found field constraint and backbone declaration for field: " ^ v)
	  else fcs', unconstr_fields
	else fcs', unconstr_fields) (fcs, []) env
    in 
    let _ = if not !CmdLine.callbohne then 
      Util.msg("\nField constraint analysis:" ^
		 "\n   backbone: " ^ String.concat ", " bb_fields ^
		 "\n   derived: " ^ String.concat ", " (List.map (fun (v,_) -> v) fcs) ^
		 "\n   trivial: " ^ String.concat ", " !trivial_fc ^"\n");
    in
    let (fs', g) = 
      if flag_positive options "QuantInst" then
	instantiate_quantifiers env unconstr_fields (fs', g) 
      else fs', g
    in
    let (fs', g), sub = 
      if flag_positive options "KeepSpecVars" then
	elim_free_vars false ~avoid_subst:unconstr_fields [] (fs', g) 
      else elim_free_vars false [] (fs', g) 
    in
    (*let _ = print_endline (PrintForm.string_of_form (form_of_sequent (fs',g))) in*)
    let derived, final_env, filtered_subst = 
      List.fold_right 
	(fun (v, ty) (derived, env, filtered_subst) -> 
	  try 
	    let fld_def, is_deterministic = List.assoc v fcs' in
	    let fv_fld_def = fv fld_def in
	    (* avoid cyclic definitions of derived fields by filtering out substitutions that mention v *)
	    let filtered_subst', sub' = 
	      List.partition (fun (x, f) -> List.mem x fv_fld_def && List.mem v (fv f)) sub
	    in
	    ((v, ty), (Some (subst sub' fld_def), is_deterministic)) :: derived, 
	    env, 
	    Util.union filtered_subst' filtered_subst
	  with Not_found -> derived, (v, ty)::env, filtered_subst)
	env ([], [], [])
    in    
    let filtered_eqs = 
      List.rev_map 
	(fun (v, f) ->
	  let ty = List.assoc v env in
	  mk_eq (TypedForm (mk_var v, ty), TypedForm (f, ty))) 
	filtered_subst
    in   
    valid final_env derived (optimize_rep bb_fields) field_types options (smk_impl (smk_and (fs' @ filtered_eqs), g))
  with 
  | Invalid_argument msg -> Util.msg ("Failed to prove sequent:\n" ^ msg); None
  | End_of_file -> Util.msg ("Failed to complete proof of sequent in given time:\n" ^ string_of_sequent (fs, g)); None
  (* | Failure str -> Util.msg str; None *)
