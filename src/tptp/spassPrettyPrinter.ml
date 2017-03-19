(** Printing {!Form} formulas to Spass format. *)

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

let default_opts () : options_t = 
  let foo = [("TimeOut", string_of_int !CmdLine.timeout);
	     ("MemoryLimit", "2000000000");
	     ("PairAxioms", "no");
	     ("Simplifications", "yes");
	     ("Splitting", "yes");
	     ("TranslationMode", "FunctionSymbols");
	     ("SortGuards", "no");
	     ("SpassSortGuards", "no");
	     ("SortImpactStat", "no")
	    ] in
    map_of_list foo

(** left flag implies right flags *)    
let flags_implications = [ ("OrderAxioms", "LtNotEqAxiom") ]

let rec subsuming (o:options_t) : (string*string) list -> options_t = 
  ListLabels.fold_left ~f:(fun o (a,b) -> if flag_positive ~o a then StringMap.add a b o else o) ~init:o 

let spass_var_ident =
  let is_capitalized = 
    let cap_string = Str.regexp "[A-Z]" in
    function s -> Str.string_match cap_string s 0 in
  function s -> 
      let cap_s = String.capitalize (Util.replace_dot_with_uscore s) in
      if is_capitalized s then cap_s else "_" ^ cap_s

let spass_const_ident s = String.uncapitalize (Util.replace_dot_with_uscore s)

let total_proof_obligations = ref 0

let fresh_uppercase_ident i = 
  Util.fresh_name (String.capitalize i ^ "_spass")
       
let fresh_lowercase_ident i = 
  Util.fresh_name (String.uncapitalize i ^ "_spass")

(** walk through the formula to register all the symbols *)

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


let print_list_of_symbols (chn:out_channel) : unit = 
 
  let f_names = ref [] in
    Hashtbl.iter (fun name sorts -> f_names := Printf.sprintf "(%s, %d)" (spass_const_ident name) (List.length (snd sorts)) :: !f_names ) func_syms;
    let p_names = ref [] in
      Hashtbl.iter (fun name sorts -> p_names := Printf.sprintf "(%s, %d)" (spass_var_ident name) (List.length sorts) :: !p_names ) predicates;   
      output_string chn "list_of_symbols.\n"; 

      if !f_names <> [] then begin
	output_string chn "functions[";
	output_string chn (String.concat ", " !f_names);
	output_string chn "].\n"
      end;

      if !p_names <> [] then begin
	output_string chn "predicates[";
	output_string chn (String.concat ", " !p_names);
	output_string chn "].\n";
      end;
      
      output_string chn "sorts[int,obj,bool,float,unknown_sort].\n";
      output_string chn "end_of_list.\n\n"


 let string_of_sort : basesort -> string = function
    | `B -> "bool"
    | `I -> "int"
    | `O -> "obj"
    | `F -> "float"
    | `Unknown -> "unknown_sort"
    | `Tuple _ -> failwith "Problem : a tuple survived !"

let print_list_of_declarations (chn:out_channel) : unit = 
  let constant_sort c s =
    if s = `Unknown then 
      Util.warn ("sort information incomplete for constant : " ^ c)
    else
      output_string chn (string_of_sort s ^ "(" ^ spass_const_ident c ^ ").\n");
  in
  let predicate_sort p args = 
    if args <> [] then fprintf chn "predicate(%s, %s).\n" (spass_var_ident p) (String.concat ", " (ListLabels.map ~f:string_of_sort args))
  in

  let function_sort f s args = 
    if (f = "fst" || f = "snd" || f="pair_tr") then () else begin
    if s = `Unknown then Util.warn ("sort information incomplete for function : " ^ f);
    let named_args = 
      let rec foo v = function
	| [] -> []
	| s::tail -> (s, List.hd v)::(foo (List.tl v) tail)
      in
	foo ["v__"; "i__"; "k__"; "t__"; "o__" ; "r__"] args
    in
    let pos = sprintf "%s(%s(%s))" (string_of_sort s) (spass_const_ident f) (String.concat ", " (ListLabels.map ~f:snd named_args)) in
    let negs = String.concat ", " (ListLabels.map ~f:(fun (s,v) -> sprintf "%s(%s)" (string_of_sort s) v) named_args) in
      fprintf chn "forall([%s], %s).\n" negs pos
    end
  in
  let print_decl name = function
    | s, [] -> constant_sort name s
    | s, l -> function_sort name s l

  in
    output_string chn "list_of_declarations.\n";
    Hashtbl.iter print_decl func_syms;
    Hashtbl.iter predicate_sort predicates;
    output_string chn "end_of_list.\n\n"




(** (FOL) form -> string *)
  let spass_pretty_print (f : fol_formula) ~options : string = 
  let rec p s = "(" ^ s ^ ")" 

  and print_term : term -> string = function
    | _, `Int k -> string_of_int k
    | _, `Variable v -> spass_var_ident v
    | _, `Constant c -> spass_const_ident c
    | _, `Function (f, args) -> sprintf "%s(%s)" (spass_const_ident f) (String.concat ", " (ListLabels.map ~f:print_term args))
    
  and print_bool : boool -> string = function
    | `True -> "true"
    | `False -> "false"
    | `BoolVar v -> spass_var_ident v
    | `NegatedBoolVar v -> "not" ^ p (spass_var_ident v)
	
	  
  and print_atom : fol_atom -> string = function
    | `Predicate (p, args) -> sprintf "%s(%s)" (spass_var_ident p) (String.concat ", " (ListLabels.map ~f:print_term args)) 
    | `Equality (t1, t2) -> sprintf "equal(%s, %s)" (print_term t1) (print_term t2)
			    

  and spass_pretty_print_binder b vars f =
    let v_names = 
      if flag_positive ~o:options "SpassSortGuards" then
	String.concat ", " (List.map (function 
					| (v,`Unknown) -> spass_var_ident v
					| (v,s) -> string_of_sort s ^ "(" ^ spass_var_ident v ^ ")"
				     ) vars) 
      else
	String.concat ", " (List.map (fun (v,_) -> spass_var_ident v) vars)
    in
    b ^ p (" [" ^ v_names ^ "], " ^ foo f)
  

  and foo : fol_formula -> string = function
    | `Forall (v, f) -> spass_pretty_print_binder "forall" v f
    | `Exists (v, f) -> spass_pretty_print_binder "exists" v f
    | #boool as b -> print_bool b
    | #fol_atom as a -> print_atom a
    | `Conjunction fs -> "and" ^ p (String.concat ", " (ListLabels.map ~f:foo fs))
    | `Disjunction fs -> "or" ^ p (String.concat ", " (ListLabels.map ~f:foo fs))
    | `Negation f -> "not" ^ p (foo f)
  in
    foo f
 

let spass_pretty_print_sequent (chn : out_channel) ~options ~(hyps : (form*fol_formula) list) ((old_goal, new_goal) : form*fol_formula) =
  ListLabels.iter ~f:(fun (old_f, new_f) -> fprintf chn "%% %s\n\nformula(%s).\n\n" (PrintForm.string_of_form (unnotate_all_types old_f)) (spass_pretty_print ~options new_f)) hyps;
  output_string chn "end_of_list.\n\n\n";

  output_string chn "list_of_formulae(conjectures).\n";
  fprintf chn "%% %s\n\nformula(%s)." (PrintForm.string_of_form (unnotate_all_types old_goal)) (spass_pretty_print ~options new_goal);
  output_string chn "end_of_list.\n"


let total_proof_obligations = ref 0
let successfull_proof_obligations = ref 0

exception Satisfiable

let interpret_result quiet (chn : in_channel) : bool option = 
  try
    let valid_regexp = Str.regexp "SPASS beiseite: Proof found" in
    let sat_regexp = Str.regexp "SPASS beiseite: Completion found" in
    let line = ref "" in 
      while true do 
	line := input_line chn;
	if Str.string_match valid_regexp !line 0 then raise Exit;
	if Str.string_match sat_regexp !line 0 then raise Satisfiable;
      done; None
  with 
    | Exit -> Some true
    | Satisfiable -> if not quiet then Util.amsg "s"; None
    | End_of_file -> None
	  
	
let invocation_string ~(options:options_t) : string = 
  let timeout = int_of_string (StringMap.find "TimeOut" options) in
  let memory_limit = StringMap.find "MemoryLimit" options in
  "SPASS -Memory=" ^ memory_limit ^ " -CNFRenMatch=0 -TimeLimit=" ^ (string_of_int timeout) 

      
let decide_sq_proper (sqob : sq_obligation) ~(options:options_t) : bool option =
  let options = subsuming (merge_opts (default_opts ()) options) flags_implications in
  let quiet = flag_positive ~o:options "Quiet" in
  let msg = if quiet then (fun _  -> ())  else Util.msg in
  let print = if quiet then (fun _  -> ())  else print_string in
  if flag_positive ~o:options "Debug"then Debug.set_debug_module "SPASS";


   

    let sq_form : form = form_of_sequent sqob.sqob_sq in

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

    let f0 = unlambda (form_of_sequent (hyps', goal)) in
    let f1 =  
      if flag_positive ~o:options "KeepRtrancl" then
(*	smart_abstract_constructs [(Const FieldRead, 1)] (RtranclTranslation.rewrite_rtrancl f0 false)  *)
	(RtranclTranslation.rewrite_rtrancl f0 false)
      else
	f0 
    in 

    let hyps', goal = sequent_of_form f1 in
      
    let (generated_axioms, hyps, goal) = FolTranslation.fol_of_form (hyps', goal) ~options in
      (* printf "FolTranslatio gets %d and gives %d hyps\n" (List.length hyps') (List.length hyps); *)

      let to_prove = if flag_positive options "Splitting" then ListLabels.map ~f:(fun f -> fst goal, f) (FolTranslation.split_form (snd goal)) else [goal] in
      let k = List.length to_prove in
	if k > 1 then msg (sprintf "[Splitting : %d pieces]" k);
	
	let run acc subgoal =
	  incr total_proof_obligations ; 
	  let sort_suffix = 
	    if flag_positive options "SpassSortGuards" then "withsorts" 
	    else "nosorts" in
	  let vc_spass_in = Util.tmp_name (sprintf "vc.spass.%s.%04d.in" 
					     sort_suffix
					     !total_proof_obligations) in
	  let vc_out = Util.tmp_name (sprintf "vc.spass.%s.%04d.out" 
					sort_suffix
					!total_proof_obligations) in 

	  let chn = open_out vc_spass_in in
	  let stripped = Str.global_replace (Str.regexp_string "\n") "\n% " (PrintForm.string_of_form sq_form) in
	    output_string chn (sprintf "%% original : %s \n\n\n"  stripped) ;
	    
	    output_string chn "begin_problem(jahob).\n";
	    output_string chn "list_of_descriptions.\n";
	    output_string chn "name({*a Jahob proof obligation*}).\n";
	    output_string chn "author({* The Jahob (tm) system *}).\n";
	    output_string chn "status(unknown).\n";
	    output_string chn "description({* Hey, do you expect *ME* to write a description ? In your dreams ! Come back in 1000 years !!!*}).\n";
	    output_string chn "end_of_list.\n\n";
	    (* assumption filtering *)
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
	      
	      (* register the symbols *)
	      Hashtbl.clear predicates;
	      Hashtbl.clear func_syms;
	      ListLabels.iter ~f:(fun (_,f) -> walk_formula f) hyps;
	      walk_formula (snd goal);
	      ListLabels.iter ~f:walk_formula generated_axioms;
	      ListLabels.iter ~f:walk_formula (TptpPrettyPrinter.static_axioms ~o:options);  
	      
	      print_list_of_symbols chn;
	      
	      if flag_positive ~o:options "SpassSortGuards" then 
		begin
		  (* printf "\nusing SPASS sort system\n"; *)
		  print_list_of_declarations chn;
		end;

	    let axioms = generated_axioms @ (TptpPrettyPrinter.static_axioms ~o:options) in
	    let axioms_translated = ListLabels.map ~f:(spass_pretty_print ~options) axioms in
	      output_string chn "list_of_formulae(axioms).\n";
	    
	      ListLabels.iter ~f:(fun s -> fprintf chn "formula(%s).\n" s) axioms_translated ;
	    
	      spass_pretty_print_sequent chn ~options ~hyps subgoal;
		
	      output_string chn "end_problem.\n";
		
	      close_out chn; 
	      flush_all ();
	      let now = Unix.gettimeofday () in
		
	      let vc_in = vc_spass_in in
	      let redirection = " > " ^ vc_out in
	      (* let timeout = int_of_string (StringMap.find "TimeOut" options) in *)
	      let _ = Util.run_command (invocation_string ~options ^ " " ^ vc_in ^ redirection) in
	      let delta =  Unix.gettimeofday () -. now in
		  if delta > 1.0 then ( 
		    print "o";
		    msg (sprintf "\nthe Prover has run for %f seconds\n" delta)
		  );		      
		  
		  let chn = open_in vc_out in
		  let res = interpret_result quiet chn in
		    close_in chn; if k > 1 then print "x" ; 
		  if Util.safe_unsome false acc then res else acc
	in
	  
	(* the ACTUAL main code is here *)
    let res = List.fold_left run (Some true) to_prove in
    match res with
    | Some true -> res
    | _ ->
	print "!";
	let cs = extract_comments (snd sqob.sqob_sq) in
	if cs <> "" then msg ("Failed proof obligation in SPASS interface talks about: " ^ cs ^ "\n");
	res 
	
	  

let decide_sq (sqob : sq_obligation) ~(options:options_t) : bool option =
  if flag_positive ~o:options "SortImpactStat" then
    (let old_total_proof_obligations = !total_proof_obligations in
     ignore (decide_sq_proper sqob 
	       (StringMap.add "SpassSortGuards" "yes" options));
       total_proof_obligations := old_total_proof_obligations;
       decide_sq_proper sqob (StringMap.add "SpassSortGuards" "no" options))
  else decide_sq_proper sqob options

let start name = 
  total_proof_obligations := 0
  
  

let stop () = ()
(*  if !total_proof_obligations <> 0 then Util.amsg (Printf.sprintf "the SPASS prover(s) managed to solve %d proof obligations over %d\n" 
	!successfull_proof_obligations 
	!total_proof_obligations)  *)
	
