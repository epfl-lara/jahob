(** Decide the truth value of {!Form.form} formula
    that belongs to BAPA fragment.

    Convert {!Form.form} formula into bapa formula, then apply the algorithm {!Alpha} to convert it to Presburger arithmetic formula and then
    use decision procedure for Presburger arithmetic to decide the truth value of the formula.

   Currently using CVC Lite as PA decision procedure instead of Omega or LASH.
*)

open Common
open Form
open FormUtil
open TypeReconstruct
open TermRewrite
open Bapaform

let debug_id = Debug.register_debug_module "Bapa"
let debug_msg = Debug.debug_msg debug_id
let debug_lmsg = Debug.debug_lmsg debug_id

(* Old prover invocation:

let lashIsUnsatisfiable (f : Form.form) : bool =
  let _ = print_string ("\ninput formula:\n" ^ (PrintForm.string_of_form f) ^ "\n"); flush_all () in
  let bf = Formbapa.formToBapa f in
  let _ = print_string ("\nBAPA:\n" ^ (Alpha.string_of_form bf) ^ "\n>>>\n"); flush_all () in
  let pf = Bapapres.bapaFormToPresForm (Alpha.alpha bf) in
    Presburger.lashIsUnsatisfiable pf

let valid (f : Form.form) : bool =
  let _ = print_string ("\ninput formula:\n" ^ (PrintForm.string_of_form f) ^ "\n"); flush_all () in
  let bf = Formbapa.formToBapa f in
  let _ = print_string ("\nBAPA:\n" ^ (Alpha.string_of_form bf) ^ "\n>>>\n"); flush_all () in
  let pf = Bapapres.bapaFormToPresForm (Alpha.alpha bf) in
    Presburger.omegaIsValid pf

let decide_sq0 (sqob : sq_obligation) (sqno:int) ~(options:options_t): bool =
  valid (form_of_sequent sqob.sqob_sq)
*)

let default_opts () : options_t = 
  let bapa_defaults = [("TimeOut",  string_of_int !CmdLine.timeout);
		       ("SliceQuantAssms", "no")] 
  in map_of_list bapa_defaults


let decide_pa_formula options (af : Alpha.form) : bool option =
  let _ = debug_msg(Printf.sprintf "\n Deciding formula with %d nodes.\n" 
				     (Alpha.formula_size af)) in
  let f = bapa_to_form af in
  let _ = debug_msg ("\nBAPA output in form:\n" ^ 
		       (PrintForm.string_of_form f) ^ "\n") in
  let res_cvcl = SmtCvcl.cvcl_prove false ([], f) options in
    res_cvcl
      (*
    if not res_cvcl then 
      Presburger.omegaIsValid (Bapapres.bapaFormToPresForm abf)
    else res_cvcl
      *)

let decide_qfbapa options (af : Alpha.form) : bool option =
  let given_n = 
    try int_of_string (StringMap.find "sparse" options)
    with Not_found -> 0 
  in
  let _ = if given_n > 0 then debug_msg (Printf.sprintf "\n sparse=%d\n" given_n) in
  let iterative = flag_positive options "iterative" in
  let check f = Util.safe_unsome false (decide_pa_formula options f) in 
  Qfbapa.check_qfbapa given_n iterative check af


let rewrite_non_bapa_atoms =
  let is_bapa_type ty = 
    match normalize_type ty with
    | TypeApp (TypeBool, [])
    | TypeApp (TypeObject, [])
    | TypeApp (TypeInt, [])
    | TypeApp (TypeSet, [TypeApp (TypeObject, [])]) ->  true
    | _ -> false  
  in
  let is_bapa_const = function
  | BoolConst _ | IntConst _ 
  | Lt | Gt | LtEq | GtEq 
  | UMinus | Plus | Minus | Mult | Div | Mod 
  | NullConst | Seteq | Eq | Old 
  | Form.Elem | Subseteq
  (* | FieldWrite | FieldRead *)
  | Card | Cardeq | Cardleq | Cardgeq
  | EmptysetConst | UniversalSetConst | FiniteSetConst 
  | Cap | Cup | Form.Diff -> true
  | _ -> false
  in
  rewrite_non_theory_atoms is_bapa_type is_bapa_const

let slice_cone env (asms, conc) =
  let fv_conc = fv conc in
  let ignored = Util.difference [Ast.all_alloc_objs; Jast.objectName] fv_conc in
  let rec collect vs =
    let vs' = List.fold_left 
	(fun vs f ->
	  match f with
	  | App (Const Elem, [Var _; Var v]) 
	  | App (Const Elem, [TypedForm (Var _, _); TypedForm (Var v, _)]) 
	  | App (Const Not, [App (Const Elem, [Var _; Var v])])
	  | App (Const Not, [App (Const Elem, [TypedForm (Var _, _); TypedForm (Var v, _)])])
	    when not (List.mem v vs) -> vs
	  | App (Const Not, [App (Const Eq, [Var v1; Var v2])]) -> vs
	  | _ -> 
	      let fv_f = fv f in
	      if List.exists (fun v -> List.mem v vs) fv_f then
		Util.union (Util.difference fv_f ignored) vs
	      else vs
	) vs asms
    in if Util.difference vs' vs = [] then vs else collect vs'
  in 
  let cone = collect (fv conc) in
  (* let _ = print_endline "Cone:" in
  let _ = List.iter (Printf.printf "%s, ") cone in *)
  let keep asms' hyp =
    let fv_hyp = fv hyp in
    if List.for_all (fun v -> not (List.mem v cone)) fv_hyp then asms' else
    match unnotate_all_types hyp with
    | App (Const Elem, [Var _; Var v]) 
    (*| App (Const Not, [App (Const Elem, [Var _; Var v])]) *)
      when not (List.mem v cone) -> asms'
    | App (Const Not, [App (Const Eq, [Var v1; Var v2])])
	when not (List.mem v1 cone && List.mem v2 cone) -> asms' 
    | _ -> hyp :: asms'
  in	  
  List.fold_left keep [] asms, conc

let slice_quant_asms (asms, conc) =
  let rec no_quant = function
    | App (f, fs) ->
       List.for_all no_quant (f::fs)
    | TypedForm(f, _)
    | Binder(Lambda, _, f)
    | Binder(Comprehension, _, f) ->
	no_quant f
    | Binder _ -> false
    | _ -> true
  in
  List.filter no_quant asms, conc

(** The main function for deciding {!Form.form} formulas
    that belong to BAPA fragment. *)
let decide_sq (env0 : typeEnv) (sqob : sq_obligation) (sqno:int) 
    ~(options:options_t) : bool option =
  let options = merge_opts (default_opts ()) options in
  (* let _ = debug_msg ("Input:\n"^(FormUtil.string_of_sequent sqob.sqob_sq)^"\n") in
  let _ = debug_msg ("in the environment: "^(String.concat ",  " (List.map (fun (v,ty)->(v^" :: "^(PrintForm.string_of_type ty))) env0))^".\n") in *)
  let sq0 = sqob.sqob_sq in
  (* Eliminate free variables - substitute definition equality assumptions *)
  (* let s = elim_fv_in_seq false sq0 in *)
  let envMap = LargeFormUtils.typeEnv2mapVarType env0 in
  let s, envMap1 = match (CardSetComp.elim_fv_in_seq_for_bapa sq0 envMap) with Some (s,e) -> (s,e) | None -> (sq0,envMap) in
  let _ = debug_msg ("After eliminating free vars:\n"^(FormUtil.string_of_sequent s)^"\n") in
  let _ = debug_msg ("in the environment: "^(LargeFormUtils.string_of_mapVarType envMap1)^".\n") in
  let sq1 = CardSetComp.remove_toplevel_cardinalities_of_finite_comprehensions s envMap1 options in
  (* Get types *)
  let fs = FormUtil.form_of_sequent (* s *) sq1 in
  let f = match fs with 
      TypedForm _ -> fs | _ -> TypedForm(fs, TypeApp(TypeBool, [])) in
  let f, env1 = TypeReconstruct.reconstruct_types (get_annotated_types f) f in
  (* Resolve ambiguous operators and remove lambda abstraction *)
  let f0 = TypeReconstruct.disambiguate (unlambda f) in
  (* let _ = debug_msg ("Before rewriting:\n"^(PrintForm.string_of_form f0)^".\n") in *)
  (* Rewrite set expressions and higher order constructs *)
  let rewrite_rules =
    [rewrite_function_eq;
     rewrite_pointsto;
     rewrite_FieldRead_FieldWrite]
  in
  let f1, env_useless = 
    try TermRewrite.rewrite true rewrite_rules env1 f0
    with _ -> f0, env1 in 
  let _ = debug_msg ("After rewriting:\n"^(PrintForm.string_of_form (elim_quants f1))^"\n") in
  let f2 = remove_comments_and_typedform f1 in
  let f21, env_useless =
    TermRewrite.rewrite true [rewrite_non_bapa_atoms] env_useless (elim_quants f2)
  in
  (* let _ = print_endline "After elimination:\n"; PrintForm.print_form f21 in *)
  let f3, env2 = reconstruct_types env_useless f21 in
  let sq3 = sequent_of_form f3 in
  (* Slice assumptions in resulting formula *)
  let sq4 = 
    if flag_positive options "SliceQuantAssms" 
    then slice_quant_asms sq3 else sq3
  in
  let sq5 = slice_cone env2 sq4 in
  (* Eliminate free variables introduced during rewriting *)
  let sq6 = elim_fv_in_seq false sq5 in
  let f7 = form_of_sequent sq6 in
  (* let _ = print_endline "After slicing:\n"; PrintForm.print_form f7 in *)
  let f8 = (* smart_abstract_constructs [(mk_null, 0)]*) f7 in
  let env3 = 
    let free_vars = fv f8 in
    List.filter (fun (v, _) -> List.mem v free_vars) env2
  in
  let bf = Formbapa.form_to_bapa false env3 (unnotate_all_types f8) in
  (* let _ = debug_msg ("\nBAPA input:"); show_bf bf in *)
  let _ = flush_all () in
    (* invoke QFBAPA if possible, otherwise full BAPA *)
  let bf_nnf = Alpha.negation_normal_form bf in
  (* let _ = debug_msg("NNF:"); show_bf bf_nnf in *)
  let bf0 = Alpha.get_quantifier_free bf_nnf 
  in
    match bf0 with
    | Some bf1 -> 
	(debug_msg "\nObtained QFBAPA formula.";
	 if flag_positive options "fullbapa" then
	   (debug_msg "\nNevertheless, due to fullbapa option using full BAPA.\n";
	    decide_pa_formula options (Alpha.alpha bf))
	 else 
	   (debug_msg "Using QFBAPA procedure.\n";
	    decide_qfbapa options bf1))
    | None -> 
	if flag_positive options "qfbapa" then
	  (debug_msg ("Due to 'qfbapa' command line option " ^
		     "approximating BAPA with QFBAPA.");
	   decide_qfbapa options (Alpha.approximate_quantifier_free bf_nnf))
	else 
	  (debug_msg "\nUsing full BAPA decision procedure.\n";
	   decide_pa_formula options (Alpha.alpha bf))


(** estimate whether BAPA is useful for deciding given sequent *)
let is_useful_dp env (_, conc) : bool =
  let bapa_consts = [Card; Cardeq; Cardleq; Cardgeq] in
  let cs_conc = consts conc in
  not (Util.disjoint cs_conc bapa_consts)
