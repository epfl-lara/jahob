(** Printing {!Form} formulas to TPTP format. *)

open Form
open FormUtil
open Printf
open FolTranslation
open Common

(* Possible Flags : 
   TimeOut [ default 5]
   PairAxioms [default on] 
   OrderAxioms [default off] 
   ArithAxioms [default off] 
   TranslationMode [default FunctionSymbols but Predicates is possible]
   ParadoxInteractive [default off]
   Spliting [default on]
   SortGuards [default off]
   Debug [default off]
*)

type prover_type = E | Vampire | Paradox | Paradox_1_3

let default_opts () : options_t = 
  let foo = [("TimeOut", string_of_int !CmdLine.timeout);
	     ("PairAxioms", "no");
	     ("Simplifications", "yes");
	     ("Splitting", "yes");
	     ("TranslationMode", "FunctionSymbols");
	     ("SortGuards", "yes");
	     ("SpassSortGuards", "yes")
	    ] in
    map_of_list foo

(** left flag implies right flags *)    
let flags_implications = [ ("OrderAxioms", "LtNotEqAxiom") ]

let rec subsuming (o:options_t) : (string*string) list -> options_t = 
  ListLabels.fold_left ~f:(fun o (a,b) -> if flag_positive ~o a then StringMap.add a b o else o) ~init:o 

(** input formats of supported provers *)
let input_format = function 
  | Vampire | E | Paradox_1_3 | Paradox -> "tptp"

let tptp_var_ident s = 
  String.capitalize (Util.replace_dot_with_uscore s)

let tptp_const_ident s = String.uncapitalize (Util.replace_dot_with_uscore s)

let total_proof_obligations = ref 0

let fresh_uppercase_ident i = 
     Util.fresh_name (String.capitalize i ^ "_tptp")
       
let fresh_lowercase_ident i = 
     Util.fresh_name (String.uncapitalize i ^ "_tptp")

let fof_formula = function
  | Paradox_1_3 -> "input_formula"
  | _ -> "fof"


let predicates = Hashtbl.create 10
let func_syms = Hashtbl.create 10

let rec walk_term : term -> unit = function
  | _, `Int k -> Hashtbl.replace func_syms (string_of_int k) (`I, [])
  | _, `Variable _ -> ()
  | s, `Constant c -> Hashtbl.replace func_syms c (s, [])
  | s, `Function (f, args) -> Hashtbl.replace func_syms f (s, ListLabels.map ~f:fst args); ListLabels.iter ~f:walk_term args

let walk_atom : fol_atom -> unit = function
  | `Equality (t1, t2) -> walk_term t1 ; walk_term t2
  | `Predicate (p, args) -> Hashtbl.replace predicates p (ListLabels.map fst args); ListLabels.iter ~f:walk_term args

let rec walk_formula : fol_formula -> unit = function
  | `Forall (v, f) -> walk_formula f
  | `Exists (v, f) -> walk_formula f
  | `NegatedBoolVar b
  | `BoolVar b -> Hashtbl.replace predicates b [] 
  | #fol_atom as a -> walk_atom a
  | `Conjunction fs -> ListLabels.iter ~f:walk_formula fs 
  | `Disjunction fs -> ListLabels.iter ~f:walk_formula fs 
  | `Negation f -> walk_formula f
  | `False
  | `True -> ()


 let string_of_sort : basesort -> string = function
    | `B -> "bool"
    | `I -> "integer"
    | `O -> "object"
    | `F -> "float"
    | `Unknown -> "unknown_sort"
    | `Tuple _ -> failwith "Problem : a tuple survived !"



(** (FOL) form -> string *)
let tptp_pretty_print (tptp_var : prover_type) (f : fol_formula) : string = 

  let rec p s = "(" ^ s ^ ")" 

  and print_term : term -> string = function
    | _, `Int k -> string_of_int k
    | _, `Variable v -> tptp_var_ident v
    | _, `Constant c -> tptp_const_ident c
    | `Tuple _, _ -> failwith "broken : tuple survived !"
    | _, `Function (f, args) -> sprintf "%s(%s)" (tptp_const_ident f) (String.concat ", " (ListLabels.map ~f:print_term args))
    
  and print_bool : prover_type -> boool -> string = function
    | Paradox_1_3 -> (let x = fresh_lowercase_ident "paradx" in function
		    | `True -> sprintf "equal(%s,%s)" x x
		    | `False -> sprintf "~equal(%s,%s)" x x
		    | `BoolVar v -> tptp_const_ident v
		    | `NegatedBoolVar v -> "~" ^ tptp_const_ident v
		 )
    | Vampire | Paradox -> (function
		    | `True -> "true"
		    | `False -> "false"
		    | `BoolVar v -> tptp_const_ident v
		    | `NegatedBoolVar v -> "~" ^ tptp_const_ident v
		 )
   
    | E ->  (function
	       | `True -> "$true"
	       | `False -> "$false"
	       | `BoolVar v -> tptp_const_ident v
	       | `NegatedBoolVar v -> "~" ^ tptp_const_ident v
	    )
	  
  and print_atom : fol_atom -> string = function
    | `Predicate (p, args) -> sprintf "%s(%s)" (tptp_const_ident p) (String.concat ", " (ListLabels.map ~f:print_term args)) 
    | `Equality (t1, t2) -> (match tptp_var with 
			       | Paradox -> sprintf "equal(%s, %s)" (print_term t1) (print_term t2)
			       | _ -> sprintf "(%s = %s)" (print_term t1) (print_term t2)
			    )

  and tptp_pretty_print_binder b vars f =
    let v_names = String.concat ", " (List.map (fun (v,s) -> tptp_var_ident v) vars) in
    p ( b ^ " [" ^ v_names ^ "] : " ^ p (foo f))
  

  and foo : fol_formula -> string = function
    | `Forall (v, f) -> tptp_pretty_print_binder "!" v f
    | `Exists (v, f) -> tptp_pretty_print_binder "?" v f
    | #boool as b -> print_bool tptp_var b
    | #fol_atom as a -> print_atom a
    | `Conjunction fs -> p (String.concat " & " (ListLabels.map ~f:foo fs)) 
    | `Disjunction fs -> p (String.concat " | " (ListLabels.map ~f:foo fs)) 
    | `Negation f ->  (match tptp_var with  	  
    			 | Vampire -> p ( foo f ^ " => false" )
			 | _ -> "~" ^ p (foo f)
		      )

  in
    foo f
 

let print_list_of_declarations ~p (chn:out_channel) : unit = 
  let constant_sort c s =
    if s = `Unknown then 
      Util.warn ("sort information incomplete for constant : " ^ c)
    else
      let axiom_name = "sort_info_" ^  tptp_const_ident c in
      let a = `Predicate (string_of_sort s, [s, `Constant c]) in

      fprintf chn "%s(%s, hypothesis, %s).\n" (fof_formula p) axiom_name (tptp_pretty_print p a);
  in
 
  let function_sort f s args = 
    if (f = "fst" || f = "snd" || f="pair_tr") then () else begin
    if s = `Unknown then Util.warn ("sort information incomplete for function : " ^ f);
    let named_args : (ident * basesort) list = 
      let rec foo v = function
	| [] -> []
	| s::tail -> ((List.hd v), s)::(foo (List.tl v) tail)
      in
	foo ["v__"; "i__"; "k__"; "t__"; "o__" ; "r__"] args
    in
    let var_args = ListLabels.map ~f:(fun (v, s) -> (s, `Variable v)) named_args in
    let a :fol_formula = `Forall (named_args, `Predicate (string_of_sort s, [s, `Function (f, var_args)])) in
    let axiom_name = "sort_info_" ^  tptp_const_ident f in
      fprintf chn "%s(%s, hypothesis, %s).\n" (fof_formula p) axiom_name (tptp_pretty_print p a);
    end
  in
  let print_decl name = function
    | s, [] -> constant_sort name s
    | s, l -> function_sort name s l
  in
    output_string chn "% ================\n% sort axioms\n\n";
    Hashtbl.iter print_decl func_syms;
    output_string chn "% ================\n% End of sort axioms\n\n"



let tptp_pretty_print_sequent (tptp_var : prover_type) (hyps : (form*fol_formula) list) ((old_goal, new_goal) : form*fol_formula) =
  let goal_string = sprintf "%% %s\n\n%s(goal, conjecture, %s)." (PrintForm.string_of_form (unnotate_all_types old_goal)) (fof_formula tptp_var) (tptp_pretty_print tptp_var new_goal)
  in 
  let hyps_string = 
    String.concat "\n\n\n" 
      (List.map 
	 (fun (old_f, new_f) -> sprintf "%% %s\n\n%s(%s, hypothesis, %s)." (PrintForm.string_of_form (unnotate_all_types old_f)) (fof_formula tptp_var) (fresh_lowercase_ident "hyp") (tptp_pretty_print tptp_var new_f))
	 hyps
      ) 
  in
    hyps_string ^ "\n\n\n\n" ^ goal_string

let total_proof_obligations = ref 0
let successfull_proof_obligations = ref 0


let interpret_result (chn : in_channel) : prover_type -> bool option = function
  | Vampire ->
      (let result = input_line chn in
      match String.sub result 0 16 with
      | "Satisfiabi" -> None
      | "Refutation found" -> Some true
      | "Refutation not f" -> None
      | _ -> Util.msg (sprintf "Hey ! The prover failed while saying : %s\n" result); None
      )  
  | E -> 
      (try
	let line1 = input_line chn in
	let result = input_line chn in
	match (try String.sub result 0 14 with Invalid_argument _ -> "") with
	| "# Proof found!" -> Some true
	| "# No proof fou" -> None
	| _ -> Util.msg (sprintf "Hey ! The prover failed while saying : %s\n" line1); None
      with
      | e -> failwith (sprintf "something went wrong (%s)" (Printexc.to_string e))
      )

  (* caution: paradox is a model-finder, i.e. 'true' is the 'don't know' value. *) 
  | Paradox_1_3 ->
      (try
	let sat_regexp = Str.regexp ".*SATISFIABLE" in
	while not (Str.string_match sat_regexp (input_line chn) 0) do ()
	done; Some false
      with End_of_file -> None)
  | Paradox ->
      (try
	let sat_regexp = Str.regexp ".*CounterSatisfiable" in
	while not (Str.string_match sat_regexp (input_line chn) 0) do ()
	done; Some false
      with End_of_file -> None)

	
let invocation_string ~(options:options_t) (p:prover_type) : string = 
  let timeout = int_of_string (StringMap.find "TimeOut" options) in
    match p with
      | Vampire -> "vampire8 -t " ^ (string_of_int timeout)
      | E -> "eprover --tptp3-in -s -xAuto -tAuto --print-statistics --cpu-limit="  ^ (string_of_int timeout) 
      | Paradox_1_3 -> "paradox" ^ if flag_positive options "ParadoxInteractive" then " --print Model" else " --sizes 1,2,4"
      |	Paradox -> "paradox" ^ if flag_positive options "ParadoxInteractive" then " --model" else " --time " ^ (string_of_int timeout)


let mkeq ~p l r = match p with
     | Paradox_1_3 -> sprintf "equal(%s,%s)" l r
     | _ -> sprintf "(%s=%s)" l r


let static_axioms ~(o:options_t) : fol_formula list = 
  let implication (f1:fol_formula) (f2:fol_formula) : fol_formula = `Disjunction [`Negation f1; f2] in
  let equivalence (f1:fol_formula) (f2:fol_formula) : fol_formula = `Conjunction [implication f1 f2; implication f2 f1] in
  let x : term = (`I, `Variable "x") and y : term = (`I, `Variable "y") and z : term = (`I, `Variable "z") and t : term = (`I, `Variable "t") in
  let zero : term = (`I, `Int 0) and 
      one : term = (`I, `Int 1) in
  let plus (x:term) (y:term) : term = `I, `Function ("plus", [x;y]) in
  let minus (x:term) (y:term) : term = `I, `Function ("minus", [x;y]) in
  let lteq (x:term) (y:term) : fol_formula = `Predicate ("lteq", [x;y]) in
(*  let gteq (x:term) (y:term) : fol_formula = `Predicate ("gteq", [x;y]) in
  let lt (x:term) (y:term) : fol_formula = `Predicate ("lt", [x;y]) in
  let gt (x:term) (y:term) : fol_formula = `Predicate ("gt", [x;y]) in *)

  let pair_axioms : fol_formula list = 
    let pair_t = (`O, `Function ("pair_tr", [(`Unknown, `Variable "x"); (`Unknown, `Variable "y")])) in
      [ `Forall ([("x",`Unknown); ("y",`Unknown)], `Equality ((`Unknown, `Function ("fst", [pair_t])), (`Unknown, `Variable "x") ));
	`Forall ([("x",`Unknown); ("y",`Unknown)], `Equality ((`Unknown, `Function ("snd", [pair_t])), (`Unknown, `Variable "y") )) ]

  and order_axioms =
    [
  (*  `Forall ([("x",`I)], gteq x x);
      
      `Forall ([("x",`I); ("y",`I)], implication (lt x y)   (lteq x y));
      `Forall ([("x",`I); ("y",`I)], implication (gt x y)   (gteq x y));
      `Forall ([("x",`I); ("y",`I)], equivalence (gteq x y) (`Negation (lt x y)));
      `Forall ([("x",`I); ("y",`I)], equivalence (lteq x y) (`Negation (gt x y)));
      `Forall ([("x",`I); ("y",`I)], equivalence (lt x y)   (gt y x));
      `Forall ([("x",`I); ("y",`I)], equivalence (lt x y)   (gt y x));
      `Forall ([("x",`I); ("y",`I)], implication (`Conjunction [lteq  x y; lteq y x]) (`Equality (x,y))); 
      `Forall ([("x",`I); ("y",`I)], equivalence (gteq x y) (lteq  y x));
      `Forall ([("x",`I); ("y",`I); ("z",`I)], implication (`Conjunction [lteq x y; lt y z]) (lt x z)); *)

      `Forall ([("x",`I)], lteq x x);
      `Forall ([("x",`I); ("y",`I)], implication (`Conjunction [lteq x y; lteq y x]) (`Equality (x, y)));
      `Forall ([("x",`I); ("y",`I); ("z",`I)], implication (`Conjunction [lteq x y; lteq y z]) (lteq x z));

      `Forall ([("x",`I); ("y",`I)], `Disjunction [lteq x y; lteq y x]);
      `Forall ([("x",`I); ("y",`I)], equivalence (lteq  x y) (`Disjunction [`Equality (x,y); `Negation (lteq y x)]))
    ]    
  
  and lt_not_eq_axioms : fol_formula list =  [ (*`Forall ([("x",`I); ("y",`I)], implication (lt  x y) (`Negation (`Equality (x,y))))*) ]
    
  and arith_axioms : fol_formula list = [
(*      `Forall ([("x",`I); ("y",`I)], equivalence (lteq x (minus y one)) (lt x y));
      `Forall ([("x",`I); ("y",`I)], equivalence (lteq (plus x one) y) (lt x y)); *)

      `Forall ([("x",`I); ("y",`I)], 
	       equivalence 
		 (lteq x (plus y one))
		 (`Disjunction [lteq x y; `Equality (x, plus y one)])); 

      `Forall ([("x",`I); ("y",`I); ("z",`I); ("t",`I)], implication (`Conjunction [lteq x y; lteq z t]) (lteq  (plus x z) (plus y t) ));
      `Forall ([("x",`I); ("y",`I); ("z",`I); ("t",`I)], implication (`Conjunction [lteq x y; lteq z t]) (lteq  (minus x t) (minus y z) ));
      `Forall ([("x",`I); ("y",`I); ("t",`I)], implication (lteq x y) (lteq  (plus x t) (plus y t) ));
      `Forall ([("x",`I); ("y",`I); ("t",`I)], implication (lteq x y) (lteq  (minus x t) (minus y t) ));

      `Forall ([("x",`I); ("y",`I)], `Equality (plus x y, plus y x));
      `Forall ([("x",`I)], `Equality (plus x zero, x));
      `Forall ([("x",`I)], `Equality (minus x zero, x));
      `Forall ([("x",`I)], `Equality (minus x x, zero))
    ]

  in
  let raw_ax = List.concat [
      if flag_positive ~o "PairAxioms"  then pair_axioms else []; 
      if flag_positive ~o "OrderAxioms"  then order_axioms else [];
      if flag_positive ~o "LtNotEqAxiom"  then lt_not_eq_axioms else [];
      if flag_positive ~o "ArithAxioms"  then arith_axioms else [] 
    ] in

  if flag_positive ~o "SortGuards" then ListLabels.map ~f:FolTranslation.add_guard raw_ax else raw_ax 



let tptp2X_invocation_string () = "tptp2X -q 2 -d" ^ (Util.tmp_name "tptp") ^ " -f"

let convert_input (prover : prover_type) (tptp_in_file : string) : string =
  let in_format = input_format prover in
  if in_format = "tptp" then tptp_in_file else begin
    ignore (Util.run_command (tptp2X_invocation_string () ^ in_format ^ " " ^ tptp_in_file));
    let in_file = Str.replace_first (Str.regexp "\\.[^\\.]*$") ("." ^ in_format) tptp_in_file in
    in_file
  end


let output_sq  (s : sequent) ~(options:options_t) (chn : out_channel) = 
 let options = subsuming (merge_opts (default_opts ()) options) flags_implications in
 
 (* if SpassSortGuards=no -explicitely, on the cmdline-, then turn sort guards off *)
 let options = 
   if not (flag_positive ~o:options "SpassSortGuards" ) then 
     StringMap.remove "SortGuards" options 
   else
     options
 in

 let (generated_axioms, hyps, goal) = FolTranslation.fol_of_form s ~options in
   
 (* axioms *)
 let prover = E in
   ListLabels.iter 
     ~f:(fun s -> fprintf chn "%s(%s, axiom, %s).\n\n" (fof_formula prover) (fresh_lowercase_ident "axiom") s) 
     ((ListLabels.map ~f:(tptp_pretty_print prover) (generated_axioms @ (static_axioms ~o:options))));
   
 
   let hyps' = 
	    if flag_positive ~o:options "Sorting" then 
	      AssumpSort.sort_assumptions (snd goal) hyps
	    else
	      hyps
	  in
	    
	  let hyps = 
	    if flag_positive ~o:options "Filtering" then
	      (
		let ratio = int_of_string (StringMap.find "Filtering" options) in
		let n = List.length hyps' in
		let to_keep = max 1 (n * ratio / 100) in
		  (*printf "LateFiltering : keeping %d on %d\n" to_keep n; *)
		  List.rev (Common.n_first to_keep (List.rev hyps'))
	      )
	    else hyps' in

(* the rest *)
   output_string chn (tptp_pretty_print_sequent prover hyps goal);
   flush_all ();;




let decide_sq  (sqob : sq_obligation) ~(prover : prover_type) ~(options:options_t) : bool option =
  let msg = if flag_positive ~o:options "Quiet" then (fun _ -> ())  else Util.msg in
(*    printf "\noptions before : %s\n" (Common.string_of_options options); *)
  let options = subsuming (merge_opts (default_opts ()) options) flags_implications in
    if flag_positive ~o:options "Debug"then Debug.set_debug_module "TPTP";

(*    printf "options after : %s\n" (Common.string_of_options options); *)
   
    let (hyps, goal) = sqob.sqob_sq in

    let hyps' = 
      if flag_positive ~o:options "EarlyFiltering" then
	(
	  let ratio = int_of_string (StringMap.find "EarlyFiltering" options) in
	  let n = List.length hyps in
	  let to_keep = n * ratio / 100 in
	    (* printf "EarlyFiltering : keeping %d on %d\n" to_keep n; *)
	    List.rev (Common.n_first to_keep (List.rev hyps))
	)
      else hyps in
      
    let f0 = form_of_sequent (hyps', goal) in
      (* add transitive closure rewriting here *)
    let f1 =  
      if flag_positive ~o:options "KeepRtrancl" then
(*	smart_abstract_constructs [(Const FieldRead, 1)] (RtranclTranslation.rewrite_rtrancl f0 false)  *)
	(RtranclTranslation.rewrite_rtrancl f0 false)
      else
	f0 
    in 
    let hyps', goal = sequent_of_form f1 in

    let sq_form : form = form_of_sequent (hyps', goal) in
    let (generated_axioms, hyps, goal) = FolTranslation.fol_of_form (hyps', goal) ~options in
      
    let to_prove = if flag_positive options "Splitting" then ListLabels.map ~f:(fun f -> fst goal, f) (split_form (snd goal)) else [goal] in
    let k = List.length to_prove in
      if k > 1 then msg (sprintf "[Splitting : %d pieces]" k);
      
      let run acc subgoal =
	(* Util.amsg (sprintf "now going for %d\n" !total_proof_obligations); *)
	incr total_proof_obligations ; 
	
	let vc_tptp_in = Util.tmp_name (sprintf "vc.tptp.%d.in" !total_proof_obligations) in
	let vc_out = Util.tmp_name (sprintf "vc.tptp.%d.out" !total_proof_obligations) in 

	let chn = open_out vc_tptp_in in
	let stripped = Str.global_replace (Str.regexp_string "\n") "\n% " (PrintForm.string_of_form sq_form) in
	  output_string chn (sprintf "%% original : %s \n\n\n"  stripped) ;
	  
	  output_string chn "% =====================\n%  Some axioms \n% =================\n\n";

	  ListLabels.iter 
	    ~f:(fun s -> fprintf chn "%s(%s, axiom, %s).\n\n" (fof_formula prover) (fresh_lowercase_ident "axiom") s) 
	    ((ListLabels.map ~f:(tptp_pretty_print prover) (generated_axioms @ (static_axioms ~o:options))));

	  output_string chn "% =====================\n% End of axioms \n% =================\n\n";


	  (* register the symbols *)
	  Hashtbl.clear predicates;
	  Hashtbl.clear func_syms;
	  ListLabels.iter ~f:(fun (_,f) -> walk_formula f) hyps;
	  walk_formula (snd goal);
	  ListLabels.iter ~f:walk_formula generated_axioms;
	  ListLabels.iter ~f:walk_formula (static_axioms ~o:options);  
	  
	  if flag_positive ~o:options "SortGuards" then print_list_of_declarations ~p:prover chn;
	  
	  let hyps' = 
	    if flag_positive ~o:options "Sorting" then 
	      (
		AssumpSort.sort_assumptions (snd subgoal) hyps)
	    else
	      hyps
	  in
	    
	  let hyps = 
	    if flag_positive ~o:options "Filtering" then
	      (
		let ratio = int_of_string (StringMap.find "Filtering" options) in
		let n = List.length hyps' in
		let to_keep = max 1 (n * ratio / 100) in
		  (*printf "LateFiltering : keeping %d on %d\n" to_keep n; *)
		  List.rev (Common.n_first to_keep (List.rev hyps'))
	      )
	    else hyps' in
	    
	  output_string chn (tptp_pretty_print_sequent prover hyps subgoal);
	  
	  close_out chn; 
	  flush_all ();
	  
	  let now = Unix.gettimeofday () in
	    
	  let vc_in = convert_input prover vc_tptp_in in
	  let redirection = 
	    if (prover = Paradox || prover = Paradox_1_3) && flag_positive options "ParadoxInteractive" then "" else " > " ^ vc_out in
	  (* let timeout = int_of_string (StringMap.find "TimeOut" options) in *)
	  let _ = Util.run_command (invocation_string ~options prover ^ " " ^ vc_in ^ redirection) in
	  let delta =  Unix.gettimeofday () -. now in
	  if delta > 1.0 then msg (sprintf "\nthe Prover has run for %f seconds\n" delta);
	  let chn = open_in vc_out in
	  let res = interpret_result chn prover in
	  close_in chn; if k > 1 then print_string "x" ; 
	  if Util.safe_unsome false acc then res else acc
    in
      
    (* the ACTUAL main code is here *)
      let res = List.fold_left run (Some true) to_prove in
(*      Util.amsg (sprintf "done with %d\n" !total_proof_obligations); *)
      match res with
      |	Some true -> res
      |	_ ->
	  let cs = extract_comments (snd sqob.sqob_sq) in
	  if cs <> "" then msg ("Failed proof obligation in TPTP interface talks about: " ^ cs ^ "\n");
	  res
	  


let start name = 
  total_proof_obligations := 0
  
  

let stop () = ()
(*  if !total_proof_obligations <> 0 then Util.amsg (Printf.sprintf "the TPTP prover(s) managed to solve %d proof obligations over %d\n" 
	!successfull_proof_obligations 
	!total_proof_obligations)  *)
	
