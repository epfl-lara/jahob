(** Print {!Ast} tree to a string. *)

(* TODO: rewrite it using module Format or Easy_format. *)

open Ast

let pf f = PrintForm.short_string_of_form f
let qpf f = "\"" ^ PrintForm.short_string_of_form f ^ "\""


let pad = Common.padding_string
let pad_incr_length = 4
let pad_increment = String.make pad_incr_length ' '

let custom_incr_pad s =
  if String.length s <> pad_incr_length
  then invalid_arg "PrintAst.custom_incr_pad"
  else pad := !pad ^ s

let incr_pad () = custom_incr_pad pad_increment

let decr_pad () =
  pad := String.sub !pad 0 (String.length !pad - pad_incr_length)

let custom_indent s f x =
  custom_incr_pad s;
  let str = f x in
    decr_pad ();
    str

let indent f x = custom_indent pad_increment f x


(****************************************)
(* Printing basic commands and commands *)
(****************************************)


let pr_skip () = !pad ^ "skip;\n"

let pr_var_assign vac =
  !pad ^ (PrintForm.isabelle_ident vac.assign_lhs)
  ^ " := \"" ^ pf vac.assign_rhs ^ "\";\n"

let pr_alloc alc =
  !pad ^ alc.alloc_lhs ^ " := " ^ "new " ^ alc.alloc_type ^ ";\n"

let pr_array_alloc aalc =
  !pad ^ aalc.arr_alloc_lhs ^ " := newarray "
  ^ aalc.arr_alloc_type ^ "["
  ^ String.concat ", " (List.map pf aalc.arr_alloc_dims) ^ "];\n"

let pr_annot_cmd cmdname ac =
  !pad ^ cmdname ^ " " ^ ac.annot_msg ^ ": \"" ^ pf ac.annot_form ^ "\";\n"

let pr_hint_annot_cmd cmdname hac =
  !pad ^ cmdname ^ " " ^ hac.hannot_msg ^ ": \"" ^ pf hac.hannot_form ^ "\""
  ^ 
    begin
      match hac.hannot_hints with
        | [] -> ""
        | ids -> " from " ^ String.concat ", " ids
    end
  ^ ";\n"

let pr_havoc hc =
  !pad ^ "havoc " ^ String.concat ", " (List.map pf hc.havoc_regions) ^ 
    (match hc.havoc_constraint with 
       | None -> ""
       | Some f -> " suchThat " ^ pf f) ^ ";\n"

let pr_call pc =
  let external_str = 
    if pc.call_is_external then " [external]" 
    else " [internal]" in
    !pad
    ^
      begin
        match pc.callee_res with
          | None -> ""
          | Some id -> id ^ " := "
      end
    ^ pc.callee_module ^ "." ^ pc.callee_name
    ^ "(" ^ String.concat ", " (List.map pf pc.callee_args) ^ ")"
    ^ external_str ^ ";\n"

let pr_hint (TrackSpecvar {track_var=id}) = !pad ^ "track(" ^ id ^ ");\n"

let pr_instantiate ic =
  let annot = ic.instantiate_annot in
    !pad ^ "instantiate " ^ (if annot = "" then "" else annot ^ ": ")
      ^ (qpf ic.instantiate_form) ^ " with "
      ^ String.concat "," (List.map qpf ic.instantiate_with) ^ ";\n"

let pr_mp mc =
  let annot = mc.mp_annot in
    !pad ^ "mp " ^ (if annot = "" then "" else annot ^ ": ")
      ^ (qpf mc.mp_form) ^ ";\n"

let pr_basic_cmd = function
  | Skip -> pr_skip ()
  | VarAssign vac -> pr_var_assign vac
  | Alloc alc -> pr_alloc alc
  | ArrayAlloc aalc -> pr_array_alloc aalc
  | Assert hac -> pr_hint_annot_cmd  "assert" hac
  | NoteThat hac -> pr_hint_annot_cmd "noteThat" hac
  | Assume ac -> pr_annot_cmd "assume" ac
  | Split ac -> pr_annot_cmd  "split" ac
  | Havoc hc -> pr_havoc hc
  | ProcCall pc -> pr_call pc
  | Hint h -> pr_hint h
  | Instantiate ic -> pr_instantiate ic
  | Mp mc -> pr_mp mc

let rec pr_basic_cell bcell =
  (if bcell.bcell_known_before=[] then "" else
     !pad ^ "[before: " ^ pf (FormUtil.mk_and bcell.bcell_known_before) ^ "]\n")
  ^ pr_basic_cmd bcell.bcell_cmd
  ^ (if bcell.bcell_known_after=[] then "" else
       !pad ^ "[after: " ^ pf (FormUtil.mk_and bcell.bcell_known_after) ^ "]\n")

and pr_seq seq =
  !pad ^ "{\n"
  ^ indent (fun seq -> String.concat "" (List.map pr_command seq)) seq
  ^ !pad ^ "}\n"

and pr_choice ch =
  let old_pad = !pad in
    old_pad ^ "choose\n"
    ^ indent
        (fun ch -> String.concat (old_pad ^ "orchoose\n")
           (List.map pr_command ch)) ch
    ^ old_pad ^ "endchoose\n"
      
and pr_if ifc =
  !pad ^ "if ( " ^ pf ifc.if_condition ^ " )\n"
  ^ !pad ^ "then\n"
  ^ indent pr_command ifc.if_then
  ^ !pad ^ "else\n"
  ^ indent pr_command ifc.if_else
  ^ !pad ^ "endif;\n"

and pr_loop loop =
  !pad ^ "loop\n"
  ^
    begin
      match loop.loop_inv with
        | None -> ""
        | Some f -> !pad ^ "invariant " ^ pf f ^ ";\n"
    end
  ^ indent pr_command loop.loop_prebody
  ^ !pad ^ "exitunless " ^ pf loop.loop_test ^ ";\n"
  ^ indent pr_command loop.loop_postbody
  ^ !pad ^ "endloop;\n"

and pr_return ret = 
  match ret.return_exp with
    | None ->   !pad ^ "return " ^ ";\n"
    | Some f ->   !pad ^ "return " ^ pf f ^ ";\n"

and pr_pickAny pa =
    !pad ^ "pickAny " ^ PrintForm.wr_bindings pa.pa_vars
    ^ " suchThat " ^ (if pa.pa_hypAnnot = "" then "" else pa.pa_hypAnnot ^ ": ")
    ^ (Util.unsome_apply "" qpf pa.pa_hyp) ^ " {\n"
    ^ indent (fun pa -> String.concat "" (List.map pr_command pa.pa_body)) pa
    ^ !pad ^ "}\n"

and pr_pickWitness pw =
    !pad ^ "pickWitness " ^ PrintForm.wr_bindings pw.pw_vars
    ^ " suchThat " ^ (if pw.pw_hypAnnot = "" then "" else pw.pw_hypAnnot ^ ": ")
    ^ (Util.unsome_apply "" qpf pw.pw_hyp) ^ " {\n"
    ^ indent (fun pw -> String.concat "" (List.map pr_command pw.pw_body)) pw
    ^ !pad ^ "}\n"

and pr_assuming a =
    !pad ^ "assuming "
    ^ (match a.assuming_hypAnnot with None -> "" | Some s -> s ^ ": ")
    ^ (qpf a.assuming_hyp) ^ " {\n"
    ^ indent
      (fun () -> String.concat "" (List.map pr_command a.assuming_body)) ()
    ^ indent (pr_hint_annot_cmd "noteThat") a.assuming_goal
    ^ !pad ^ "}\n"

and pr_induct ic =
  let annot = ic.induct_annot in
    !pad ^ "induct " ^ (if annot = "" then "" else annot ^ ": ") 
    ^ (qpf ic.induct_form) ^ " over " ^ PrintForm.wr_binding ic.induct_var 
    ^ " {\n" ^ indent 
    (fun () -> String.concat "" (List.map pr_command ic.induct_body)) () 
    ^ !pad ^ "}\n"

and pr_contradict cc =
  let annot = cc.contradict_annot in
    !pad ^ "contradict " ^ (if annot = "" then "" else annot ^ ": ")
    ^ (qpf cc.contradict_form) ^ " {\n" ^ indent 
    (fun () -> String.concat "" (List.map pr_command cc.contradict_body)) () 
    ^ !pad ^ "}\n"

and pr_proof pc =
    !pad ^ "proof {\n"
    ^ indent
      (fun () -> String.concat "" (List.map pr_command pc.proof_body)) ()
    ^ indent (pr_hint_annot_cmd "noteThat") pc.proof_goal
    ^ !pad ^ "}\n"  

and pr_command = function
  | Basic basic_cmd -> pr_basic_cell basic_cmd
  | Seq cs -> pr_seq cs
  | Choice cs -> pr_choice cs
  | If if_cmd -> pr_if if_cmd
  | Loop loop -> pr_loop loop
  | Return ret -> pr_return ret
  | PickAny pa -> pr_pickAny pa
  | PickWitness pw -> pr_pickWitness pw
  | Assuming a -> pr_assuming a
  | Induct ic -> pr_induct ic
  | Contradict cc -> pr_contradict cc
  | Proof pc -> pr_proof pc


(**********************)
(* Printing a program *)
(**********************)

let rec pr_array_type (ty : array_type) =
  match ty with
    | BaseType id -> id
    | ArrayType ty' -> "(array of " ^ pr_array_type ty' ^ ")"

let pr_var_decl vd =
  vd.vd_name ^ " : " ^ PrintForm.string_of_type vd.vd_type
  ^ (match vd.vd_init with None -> "" | Some f -> " == " ^ pf f)
  ^ 
    begin
      let mods = List.concat 
        [if vd.vd_abstract then ["abstract"] else [];
         if vd.vd_ghost then ["ghost"] else [];
         if vd.vd_field then ["field"] else [];
	 (match vd.vd_def with None -> [] | Some f -> 
	    ["== " ^ (PrintForm.string_of_form f)]);
	 (match vd.vd_jtype with None -> [] | Some id -> ["Java type " ^ id]);
	 (match vd.vd_basetype with 
	    | None -> []
	    | Some t -> ["Array base type " ^ pr_array_type t]);
	 (match vd.vd_class with None -> [] | Some cl -> ["class " ^ cl]);
         (match vd.vd_owner with None -> [] | Some cl -> ["claimedby " ^ cl]);
         let (e, ep) = vd.vd_encap in
           if ep then ["encap+"] else if e then ["encap"] else []]
      in 
        match mods with 
	  | [] -> ""
	  | _ -> " [" ^ String.concat ", " mods ^ "]"
    end

let pr_gvar_decl vd = !pad ^ "var " ^ pr_var_decl vd ^ ";\n"

let pr_contract c =
  if c.co_resolved then
    !pad ^ "requires " ^ pf c.co_pre  ^ "\n"
    ^
      begin
        match c.co_mod with
          | None -> ""
          | Some m -> !pad ^ "modifies " ^ 
	      String.concat ", " (List.map pf m) ^ "\n"
      end
    ^ !pad ^ "ensures " ^ pf c.co_post ^ "\n"
  else !pad ^ "(* SPEC UNRESOLVED *)"

let pr_proc_header_line mname ph =
  Printf.sprintf "%s%s procedure %s (%s) : %s\n"
    !pad
    (if ph.p_public then "public" else "private")
    (Util.qualify_if_needed mname ph.p_name)
    (String.concat ", " (List.map pr_var_decl ph.p_formals))
    (PrintForm.string_of_type ph.p_restype)

let pr_proc_header mname ph =
  pr_proc_header_line mname ph ^ pr_contract ph.p_contract

let pr_vardef (v,f) = !pad ^ v ^ " == " ^ pf f ^ ";\n"

let pr_vardefs svs =
  match svs with
    | [] -> ""
    | _ -> !pad ^ "vardefs\n" ^
        indent (fun svs -> String.concat "" (List.map pr_vardef svs)) svs

let pr_constdefs svs =
  match svs with
    | [] -> ""
    | _ -> "constdefs\n" ^
        String.concat "" (List.map pr_vardef svs)

let pr_proc_def mname p =
  pr_proc_header mname p.p_header
  ^ !pad ^ "local variables:\n"
  ^ indent (fun p -> String.concat "" (List.map pr_gvar_decl p.p_locals)) p
  ^ indent pr_vardefs p.p_vardefs ^ "\n"
  ^ match p.p_body with
    | Seq cl -> pr_seq cl ^ "\n"
    | c -> "{\n" ^ indent pr_command c ^ "}\n\n"

let pr_inv inv = !pad ^ (PrintSpec.p_invariant inv) ^ "\n\n"

let pr_invs (name : string) = function
  | [] -> ""
  | invs -> "\n" ^ !pad ^ name ^ ":\n"
            ^ (String.concat "" (List.map pr_inv invs)) ^ "\n"

(* 
   let pr_hide (f : form) = 
   "hidden objects " ^ PrintForm.string_of_form f ^ ";\n"
   
   let pr_hides (hides : form list) = match hides with
   | [] -> ""
   | _ -> (String.concat "" (List.map pr_hide hides)) ^ "\n"
   
   let pr_claim (f : form) = 
   "claim locations " ^ PrintForm.string_of_form f ^ ";\n"
   
   let pr_claims (claims : form list) = match claims with
   | [] -> ""
   | _ -> (String.concat "" (List.map pr_claim claims)) ^ "\n"
*)

let pr_owner (owner : Form.ident option) =
  match owner with
    | None -> ""
    | Some id -> "claimedby " ^ id ^ "\n"

let pr_impl (im : impl_module) =
  !pad ^ "impl module " ^ im.im_name ^ "\n"
  ^ pr_owner im.im_owner
  ^ String.concat "" (List.map pr_gvar_decl im.im_vars) ^ "\n"
  ^ !pad ^ pr_constdefs im.im_constdefs
  ^ pr_vardefs im.im_vardefs
  ^ pr_invs "Invariants" im.im_invs
    (*
      pr_hides im.im_hide ^
      pr_claims im.im_claim ^
    *)
  ^ String.concat ("\n") (List.map (pr_proc_def im.im_name) im.im_procs) ^
  "\nend impl module " ^ im.im_name ^ ".\n"

let pr_spec_module (sm : spec_module) =
  !pad ^ "spec module " ^ sm.sm_name ^ "\n"
  ^ !pad ^ String.concat "" (List.map pr_gvar_decl sm.sm_spec_vars)
  ^ pr_constdefs sm.sm_constdefs
  ^ pr_vardefs sm.sm_vardefs
  ^ pr_invs "Invariants" sm.sm_invs
  ^ pr_invs "Free invariants" sm.sm_free_invs
  ^ String.concat "\n"
      (List.map (pr_proc_header sm.sm_name) sm.sm_proc_specs) ^ "\n"
  ^ !pad ^ "end spec module " ^ sm.sm_name ^ ".\n"

let pr_typeDef (td : Form.typeDef) = PrintForm.string_of_typedef td

let pr_map (m : mapping) =
  !pad ^ "refinement\n"
  ^ !pad ^ "impl " ^ m.map_impl.im_name ^ "\n"
  ^ !pad ^ "spec " ^ m.map_spec.sm_name ^ "\n\n"
  ^ pr_vardefs m.map_abst ^ "\n"
  ^ !pad ^ "end refinement.\n"

let pr_program (p : program) : string =
  "(*************************************************************)\n\
   (*                         BEGINPROGRAM                      *)\n\
   (*************************************************************)\n\
   (*                          Types                            *)\n\
   (*************************************************************)\n" ^
   String.concat "\n" (List.map pr_typeDef p.p_types) ^ "\n" ^
  "(*************************************************************)\n\
   (*                   Implementation Modules                  *)\n\
   (*************************************************************)\n" ^
   String.concat "\n" (List.map pr_impl p.p_impls) ^ "\n" ^
  "(*************************************************************)\n\
   (*                   Specification Modules                   *)\n\
   (*************************************************************)\n" ^
   String.concat "\n" (List.map pr_spec_module p.p_specs) ^ "\n" ^
  "(*************************************************************)\n\
   (*                      Refinement Conditions                *)\n\
   (*************************************************************)\n" ^
   String.concat "\n" (List.map pr_map p.p_maps) ^
  "\n\n(* ENDPROGRAM *)\n\
   (*************************************************************)\n"


(****************************************)
(* Printing simplified (normalized) ast *)
(****************************************)


let spr_impl (im : impl_module) : string =
  let mname = im.im_name in
  let spr_proc_header (ph : proc_header) =
    (if ph.p_public then "public " else "private ")
    ^ "proc " ^ mname ^ "." ^ ph.p_name
    ^ "(" ^ String.concat ", " (List.map pr_var_decl ph.p_formals) ^ ")"
    ^ " : " ^ PrintForm.string_of_type ph.p_restype ^ "\n"
  in
  let spr_proc (proc : proc_def) : string =
    match proc.p_simple_body with
      | None -> ""
      | Some b -> 
	  if List.mem (mname,proc.p_header.p_name) !CmdLine.methods_to_analyze
          then
	    spr_proc_header proc.p_header
	    ^ "local vars\n"
            ^ indent (fun () ->
                        String.concat ", " (List.map pr_var_decl proc.p_locals))
                ()
            ^ "\n" ^ !pad ^ pr_command b.sb_body
	  else ""
  in
    String.concat "" (List.map spr_proc im.im_procs)

let simplified_program (p : program) : string = 
  Util.amsg("\n\n---...---...--- Printing simplified program ---...---...\n");
  String.concat "" (List.map spr_impl p.p_impls)
