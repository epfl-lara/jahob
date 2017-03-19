(** Translate {!Ast} tree to the armc files *)

open Common
open Ast
open AstUtil
open Form
open FormUtil
open Printf


type armc_ident = {
mutable proc_name: string;
mutable  var_pre : string;
mutable  old_pre : string;
mutable  cur_suf : string;
mutable  nxt_suf : string;
}

let armc_tags : armc_ident = {
  proc_name = "main";
  var_pre = "V_";
  old_pre = "V_old_";
  cur_suf = "_0";
  nxt_suf = "_1";
}

(*Some Utils *)

let member xs x  = List.mem x xs 

let subtract xs ps  = 
  let (_,fs) = List.partition (member ps) xs  in
    fs

let extract_var_name (f : form) : string =
  match f with
    | TypedForm((Var var_name), TypeApp(TypeInt,[])) -> armc_tags.old_pre^(Util.replace_dot_with_uscore var_name)
    | _ -> print_string ("Unexpected Fromula Type "^(MlPrintForm.string_of_form f)^""); ""

let modify_var_list (mod_form : form list option) : string list =  
  match mod_form with
    | None -> []
    | Some(mod_list) ->  (List.map extract_var_name mod_list)

(*Code Dealing with string and names*)

let armc_var_name (var : var_decl) : string = armc_tags.var_pre^(Util.replace_dot_with_uscore var.vd_name)

let armc_name_map (var : var_decl) : string = "("^armc_tags.var_pre^(Util.replace_dot_with_uscore var.vd_name)^",'"^var.vd_name^"')" 

let armc_mod_var_map (var : string) : string = "("^var^",'"^var^"')" 

let suffix (suff : string) (name : string ) :string = name^suff

(*Code For Formulas*)

let transform_dnf (f : form ) : form list = [f]

let remove_old (var_name :string ) : string = 
  let name = (Util.replace_dot_with_uscore var_name) in
  let old  = String.sub name 0 4 in
    if old = "old_" then
      let len = String.length name in
      let rest = len - 4 in
      (String.sub name 4 rest)^armc_tags.cur_suf
    else
      name^armc_tags.nxt_suf

let old_remove_flag : int ref = ref 0
let rec translate_simple_form (f : form) : string = 
  match f with
    | Var (var_name) -> 
	if !old_remove_flag == 1 then
	    armc_tags.var_pre^(remove_old var_name)
	else
	    armc_tags.var_pre^(Util.replace_dot_with_uscore var_name)^armc_tags.cur_suf
    | Const(cons)    -> Form.string_of_const(cons) 
    | App( op , fl )    ->  (String.concat (translate_simple_form op) (List.map translate_simple_form fl) )
    | TypedForm( exp ,(TypeApp(TypeInt,[]))) -> translate_simple_form exp 
    | _ ->  print_string ("Ignored Formula"^(MlPrintForm.string_of_form f)); ""

let translate_form ( f : form ) : string list = 
  List.map translate_simple_form (transform_dnf f)  


(*Code writes armc output*)

let eq_exp ( var : string ) : string =  (var^armc_tags.nxt_suf^" = "^var^armc_tags.cur_suf)
let gen_trivial_update (dont_vars : string list) (vars : string list) : string list = List.map eq_exp (subtract vars dont_vars)


let cl_counter : int ref = ref 1


let write_armc_edge (oc : out_channel ) (vars : string list) (src : string) (dst : string) (relation : string) : unit = 
  let vars_0 = (String.concat "," (List.map (suffix armc_tags.cur_suf) vars)) in
  let vars_1 = (String.concat "," (List.map (suffix armc_tags.nxt_suf) vars)) in
  cl_counter := !cl_counter + 1;
  fprintf oc "%s" ("r(p(pc("^armc_tags.proc_name^"-"^src^"), data("^vars_0^")),\n");
  fprintf oc "%s" ("  p(pc("^armc_tags.proc_name^"-"^dst^"), data("^vars_1^")),\n");
  fprintf oc "%s" ("["^relation^"], [], "^(string_of_int !cl_counter)^").\n")

let write_armc_clause (oc : out_channel ) (vars : string list) (src : string) (relation : string list) (dst : string) : unit = 
  let _ = List.map (write_armc_edge oc vars src dst) relation in ()

let write_armc_header (oc : out_channel): unit = 
  fprintf oc ":- multifile r/5,implicit_updates/0,var2names/2,preds/2,trans_preds/3,cube_size/1,start/1,error/1,refinement/1,cutpoint/1.\n";
  fprintf oc "refinement(inter).\ncube_size(1).\n"

let write_preds_armc (oc : out_channel ) (var_list : string list) ( var_map : string list) : unit = 
  let var_dec  = (String.concat "," var_list) in
  let varp_dec = (String.concat "," (List.map (suffix "p") var_list) ) in
  let var_map_dec  = (String.concat "," var_map ) in
    fprintf oc "%s" ("preds(p(_,data("^var_dec^")),[]).\n");
    fprintf oc "%s" ("trans_preds(p(_, data("^var_dec^")),p(_,data("^varp_dec^")), []).\n");
    fprintf oc "%s" ("var2names(p(pc("^armc_tags.proc_name^"-_),data("^var_dec^")),["^var_map_dec^"]).\n");
    fprintf oc "%s" ("start(pc("^armc_tags.proc_name^"-assume)).\nerror(pc("^armc_tags.proc_name^"-error)).\n")



let translate_basic_command (oc : out_channel ) (vars : string list)
    (src : string) (next_pps : string list) ( b_cmd : basic_command ) : unit =
  match b_cmd with 
    | Skip -> 	
	let _ = List.map ( write_armc_clause oc vars src [(String.concat "," (gen_trivial_update [] vars))] ) next_pps in
	  ()
    | VarAssign (ass_cmd) -> 
	let assign_var  = armc_tags.var_pre^(Util.replace_dot_with_uscore ass_cmd.assign_lhs) in
	let assign_dec = assign_var^armc_tags.nxt_suf^" = "^(translate_simple_form ass_cmd.assign_rhs) in
	let _ = List.map ( write_armc_clause oc vars src [(String.concat "," (assign_dec::(gen_trivial_update [assign_var] vars)))] ) next_pps in
	  ()
    | Alloc (aloc_cmd ) -> ()
    | ArrayAlloc(_) -> ()
    | Assert ( assert_cmd ) -> 
	let update = (String.concat "," (gen_trivial_update [] vars)) in
	let cond_form = (translate_form assert_cmd.hannot_form) in
	let _ = List.map ( write_armc_clause oc vars src (List.map (suffix (","^update)) cond_form) ) next_pps in
	let neg_form  = ( translate_form (FormUtil.negation_normal_form  (App(Const Not, [assert_cmd.hannot_form]))) ) in
	let _ = List.map ( write_armc_clause oc vars src (List.map (suffix (","^update)) neg_form) ) ["error"] in
	  ()
    | NoteThat (_) -> ()
    | Assume ( assume_cmd ) -> 
	let update = (String.concat "," (gen_trivial_update [] vars)) in
	let cond_form = (translate_form assume_cmd.annot_form) in
	let _ = List.map ( write_armc_clause oc vars src (List.map (suffix (","^update)) cond_form) ) next_pps in
	()
    | Split (_) -> ()
    | Havoc (_) -> ()
    | ProcCall( proc_call) -> ()
    | Hint(_) -> ()
    | Instantiate (_) -> ()
    | Mp (_) -> ()

let translate_basic_cell (oc : out_channel ) ( vars : string list) (next_pps : string list ) (b_cell : basic_cell) : unit =
  translate_basic_command oc vars (string_of_int b_cell.bcell_point.pp_id) next_pps b_cell.bcell_cmd

let rec top_point_command ( co : command ) : string list = 
match co with
  | Basic ( b_cell ) ->    [string_of_int b_cell.bcell_point.pp_id]
  | Seq ([]) -> []
  | Seq ( sco :: scos ) -> 
      let temp_name = top_point_command sco in
	if ( (temp_name == []) && ( scos != [] )) then
	  top_point_command (Seq(scos))
	else
	  temp_name
  | Choice( co_list ) -> List.flatten (List.map top_point_command co_list)
  | If  ( if_command ) -> [string_of_int if_command.if_ppoint.pp_id]
  | Loop( lo_command ) -> [string_of_int lo_command.loop_ppoint.pp_id]
  | Return (ret_command) -> []
  | Assuming _ -> Util.fail "top_point_command: \
                             uncaught pattern matching case 'Assuming'"
  | PickAny _ -> Util.fail "top_point_command: \
                            uncaught pattern matching case 'PickAny'"
  | PickWitness _ -> Util.fail "top_point_command: \
                            uncaught pattern matching case 'PickWitness'"
  | Induct _ -> Util.fail "top_point_command: \
                           uncaught pattern matching case 'Induct'"
  | Contradict _ -> Util.fail "top_point_command: \
                               uncaught pattern matching case 'Contradict'"
  | Proof _ -> Util.fail "top_point_command: \
                          uncaught pattern matching case 'Proof'"


let rec translate_command_list (oc : out_channel ) (vars : string list) (next_pps : string list) (co_list : command list) : unit = 
  match co_list with 
    | [] -> ()
    | co::cos -> 
	let i_pps =  (top_point_command (Seq(cos)))  in 
	  if i_pps == [] then
	    translate_command oc vars next_pps co
	  else 
	    let _ = translate_command oc vars i_pps co in
	    translate_command_list oc vars next_pps cos


and translate_command (oc : out_channel ) (vars : string list) (next_pps : string list) (co : command) : unit = 
match co with 
  | Basic( b_cell ) ->   translate_basic_cell oc vars next_pps b_cell 
  | Seq ( co_list ) ->  (translate_command_list oc vars next_pps co_list)
  | Choice ( co_list) -> 
      let _ = (List.map (translate_command oc vars next_pps) co_list) in ()
  | If(if_command) -> ()
  | Loop(lo_co) -> ()
  | Return (return) -> ()
  | Assuming _ -> Util.fail "translate_command: \
                             uncaught pattern matching case 'Assuming'"
  | PickAny _ -> Util.fail "translate_command: \
                            uncaught pattern matching case 'PickAny'"
  | PickWitness _ -> Util.fail "translate_command: \
                            uncaught pattern matching case 'PickWitness'"
  | Induct _ -> Util.fail "translate_command: \
                           uncaught pattern matching case 'Induct'"
  | Contradict _ -> Util.fail "translate_command: \
                               uncaught pattern matching case 'Contradict'"
  | Proof _ -> Util.fail "translate_command: \
                          uncaught pattern matching case 'Proof'"


let translate_prepost (oc : out_channel) ( vars : string list) ( proc : proc_def) : unit = 
  let f_point = top_point_command proc.p_body in
  let update = (String.concat "," (gen_trivial_update [] vars)) in
  let pre_form = (translate_form proc.p_header.p_contract.co_pre) in
  let post_form = (translate_form proc.p_header.p_contract.co_post) in 
  let post_neg_form = translate_form
    (FormUtil.negation_normal_form (App(Const Not, 
                                        [proc.p_header.p_contract.co_post]))) in
  let _ = List.map (write_armc_clause oc vars "assume"
                      (List.map (suffix (","^update)) pre_form)) f_point in
  let _ = List.map (write_armc_clause oc vars "assert"
                      (List.map (suffix (","^update)) post_neg_form)) ["error"] in
  List.iter (write_armc_clause oc vars "assert" 
               (List.map (suffix (","^update)) post_form)) ["end"]

let translate_proc (module_name : ident) (mod_vars : var_decl list) (proc : proc_def) :unit =
  let fileout = module_name^"."^proc.p_header.p_name^".armc" in
  let oc = (open_out fileout) in
  let var_list =  List.map armc_var_name (mod_vars@proc.p_locals) in
  let modify_vars = modify_var_list proc.p_header.p_contract.co_mod in
  let var_map = List.map armc_name_map (mod_vars@proc.p_locals) in 
    print_string ("Creating file "^fileout^"\n");
    write_armc_header oc;
    write_preds_armc  oc (var_list@modify_vars) (var_map@(List.map armc_mod_var_map modify_vars));
    translate_prepost oc (var_list@modify_vars) proc;
    translate_command oc (var_list@modify_vars) ["assert"]  proc.p_body ; 
    close_out oc

let translate_module (mod_impl : impl_module): unit = 
  let _ = List.map (translate_proc mod_impl.im_name mod_impl.im_vars) mod_impl.im_procs in
    ()

(** Top-level function, prints the entire program. *)
let translate_program (p : program) : unit =
  print_string "Translating to Armc output\n";
  let _ = List.map translate_module p.p_impls in
  ()
   
