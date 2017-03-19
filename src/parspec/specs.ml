(** Abstract syntax tree for Jahob specifications. *)

open Form
open FormUtil

type contract_def =
    { c_pre  : form option;
      c_mod  : form list option;
      c_post : form option }

type abstract_var_decl = { 
  avd_name : string;
  avd_type : Form.typeForm;
  avd_init : Form.form option;
  avd_public : bool;
  avd_field : bool;
  avd_ghost : bool;
  avd_encap : bool * bool;
}

type abstract_assign = {
  aa_lhs : form;
  aa_rhs : form;
}

type var_def = ident * form

type mod_kind =
	| Readonly
	| ClaimedBy of string
	| Encap
	| EPlus
	| Hidden

type publicness = 
  | PubPublic
  | PubPrivate
  | PubDefault

type staticness =
  | StatStatic
  | StatInstance

type ghostness =
  | GhostVar
  | NonGhostVar

type encapness = 
  | EncapVar
  | EPlusVar
  | NonEncapVar

type abstract_operation = {
  ao_name : string;
  ao_args : form list;
}

type lemma_desc = {
  lemma_name : string;
  lemma_form : form;
}

type invariant_desc = {
  inv_name : string;
  inv_ensured : bool;
  inv_public : bool;
  inv_encap : bool;
  inv_form : form;
}

type annot_form = {
  af_form : form;
  af_annot : string;
}
let mk_annot_form s f = {af_form=f; af_annot=s}
let wr_annot_form af = 
  (if af.af_annot="" then "" else af.af_annot ^ ": ") ^ 
    PrintForm.quoted_form af.af_form

type noted_form = {
  nf_af : annot_form;
  nf_hints : ident list;
  nf_forSuch : ident list;
}

type noteThat_cmd = {
  nt_form : noted_form;
}

type pickAny_cmd = {
  pick_vars : (ident * typeForm) list;
  pick_assume : annot_form option;
}

type cases_cmd = {
  cases_cases : form list;
  cases_af : annot_form;
  cases_hints : ident list;
}

type showedcase_cmd = {
  showedcase_i : int;
  showedcase_af : annot_form;
  showedcase_hints : ident list;
}

type havoc_cmd = {
  hav_regions : form list;
  hav_suchThat : annot_form option;
  hav_internal : bool;
}

type induct_cmd = {
  induct_af : annot_form;
  induct_var : ident * typeForm;
}

type witness_cmd = {
  witness_witnesses : form list;
  witness_af : annot_form;
  witness_hints : ident list;
}

type instantiate_cmd = {
  instantiate_af : annot_form;
  instantiate_with : form list;
}

type spec = 
  | Lemma of lemma_desc
  | Invariant of invariant_desc
  | Contract of contract_def
  | SpecField of abstract_var_decl
  | SpecStatic of abstract_var_decl
  | SpecVar of abstract_var_decl
  | Constdefs of var_def list
  | PubConstdefs of var_def list
  | Vardefs of var_def list
  | PubVardefs of var_def list
  | Modifier of mod_kind
  | Assert of noted_form
  | NoteThat of noted_form
  | Assume of annot_form
  | PickAny of pickAny_cmd
  | PickWitness of pickAny_cmd
  | Cases of cases_cmd
  | ShowedCase of showedcase_cmd
  | Induct of induct_cmd
  | Witness of witness_cmd
  | Contradict of annot_form
  | FalseIntro of annot_form
  | Instantiate of instantiate_cmd
  | Mp of annot_form
  | Proof
  | Assuming of annot_form
  | Split of annot_form
  | Havoc of havoc_cmd
  | Have of form
  | Assign of abstract_assign
  | Operation of abstract_operation

let mk_havoc (regions : form list) (st : annot_form option) : spec =
  Havoc{hav_regions = regions;
	hav_suchThat = st;
	hav_internal = false}

let wr_havoc (ha : havoc_cmd) : string =
  "havoc " ^ String.concat ", " (List.map PrintForm.quoted_form ha.hav_regions) ^
    (match ha.hav_suchThat with
       | Some af -> " suchThat " ^ wr_annot_form af
       | None -> "")

let mk_contract pre md post = 
  Contract { c_pre = pre; c_mod = md; c_post = post }

let mk_noteThat (af : annot_form) (hs : ident list) 
    (forSuch : ident list) : spec = 
  NoteThat {nf_af=af; nf_hints=hs; nf_forSuch = forSuch}
let wr_noteThat (nf : noted_form) : string = 
  "noteThat " ^ wr_annot_form nf.nf_af ^
    (match nf.nf_hints with
       | [] -> ""
       | ids -> " from " ^ String.concat ", " ids) ^
    (match nf.nf_forSuch with
       | [] -> ""
       | ids -> " forSuch " ^ String.concat "," ids)

let mk_assert (af : annot_form) (hs : ident list) : spec = 
  Assert {nf_af=af; nf_hints=hs; nf_forSuch = []}
let wr_assert (nf : noted_form) : string = 
  "assert " ^ wr_annot_form nf.nf_af ^
    (match nf.nf_hints with
       | [] -> ""
       | ids -> " from " ^ String.concat ", " ids)

let mk_pickAny 
    (vars : (ident * typeForm) list) 
    (condition : annot_form option) : spec =
  PickAny {pick_vars=vars;
	   pick_assume = condition}

let mk_pickWitness
    (vars : (ident * typeForm) list) 
    (condition : annot_form option) : spec =
  PickWitness {pick_vars=vars;
	       pick_assume = condition}

let wr_pickAny (pa : pickAny_cmd) : string =
  "pickAny " ^PrintForm.wr_bindings pa.pick_vars^
  (match pa.pick_assume with 
     | Some f -> " suchThat "^wr_annot_form f
     | None -> "")

let mk_induct (af : annot_form) ((id, ty) : ident * typeForm) : spec =
  if not (ty = mk_int_type) then
    Util.fail ("Induction must be performed over integers. " ^
      "Cannot perform induction over type " ^ (PrintForm.string_of_type ty));
  Induct {induct_af = af; 
	  induct_var = (id, ty)}

let wr_induct (ic : induct_cmd) : string =
  "induct " ^ wr_annot_form ic.induct_af ^ 
    " over " ^ PrintForm.wr_binding ic.induct_var

let mk_witness
    (witnesses : form list)
    (af : annot_form) 
    (hs : ident list) : spec =
  Witness {witness_witnesses = witnesses;
	   witness_af = af;
	   witness_hints = hs}

let wr_witness (wc : witness_cmd) : string =
  "witness " ^ 
    String.concat ", " (List.map PrintForm.quoted_form wc.witness_witnesses) ^ 
    " for " ^ wr_annot_form wc.witness_af ^
    (match wc.witness_hints with
       | [] -> ""
       | ids -> " from " ^ String.concat "," ids)

let mk_cases 
    (cases : form list) (af : annot_form) (hints : ident list) : spec =
  Cases {cases_cases = cases;
	 cases_af = af;
	 cases_hints = hints}

let wr_cases (cc : cases_cmd) : string =
  "cases " ^ String.concat "," (List.map PrintForm.quoted_form cc.cases_cases) ^
    wr_annot_form cc.cases_af ^
    (match cc.cases_hints with
       | [] -> ""
       | ids -> " from " ^ String.concat "," ids)

let mk_showedcase
    (i : int) (af : annot_form) (hints : ident list) : spec =
  ShowedCase {showedcase_i = i;
	      showedcase_af = af;
	      showedcase_hints = hints}

let wr_showedcase (sc : showedcase_cmd) : string =
  "showedCase " ^ (string_of_int sc.showedcase_i) ^ " of " ^ 
    wr_annot_form sc.showedcase_af ^
    (match sc.showedcase_hints with
       | [] -> ""
       | ids -> " from " ^ String.concat "," ids)

let mk_instantiate (af : annot_form) (fs : form list) : spec =
  Instantiate {instantiate_af = af;
	       instantiate_with = fs}

let wr_instantiate (ic : instantiate_cmd) : string =
  "instantiate " ^ wr_annot_form ic.instantiate_af ^ " with " ^
    String.concat "," (List.map PrintForm.quoted_form ic.instantiate_with)

(*
let mk_spec_field n t i = SpecField { 
  avd_name=n; 
  avd_type=t; 
  avd_init=i;
  avd_public = true;
  avd_field = true;  
}

let mk_spec_static n t i = SpecStatic { 
  avd_name=n; 
  avd_type=t; 
  avd_init=i;
  avd_public = true;
  avd_field = false;
}
*)

let warn_deprecated_specfield() = 
  Util.warn "specfield deprecated, use specvar instead"

let warn_deprecated_specstatic() = 
  Util.warn "specstatic deprecated, use specvar instead"

let mk_specvar 
    (pns : publicness)
    (ens : encapness)
    (sns : staticness)
    (gns : ghostness)
    (id  : ident)
    (t   : typeForm)
    (oi  : form option) : spec = 
  SpecVar {
    avd_name = id;
    avd_type = t;
    avd_init = oi;
    avd_public = (pns = PubPublic);
    avd_field = (sns != StatStatic);
    avd_ghost = (gns = GhostVar);
    avd_encap = ((ens = EncapVar || ens = EPlusVar), (ens = EPlusVar)); (** (Encap, Encap+) **)
  }

let avd_of_tv ((v,t) : string * typeForm) : abstract_var_decl =
  {
    avd_name = v;
    avd_type = t;
    avd_init = None;
    avd_public = false;
    avd_field = false;
    avd_ghost = true;
    avd_encap = (false, false);
  }

let mk_def (f : form) : ident * form = match f with
  | App(Const MetaEq, [Var v;rhs]) -> (v,rhs)
  | _ -> failwith ("Expected a definition of form 'varName == formula'" ^
		     "while parsing " ^ PrintForm.string_of_form f)

let mk_constdefs (pns : publicness) (vds : var_def list) = 
  if pns = PubPublic then PubConstdefs vds
  else Constdefs vds

let mk_vardefs (pns : publicness) (vds : var_def list) = 
  if pns = PubPublic then PubVardefs vds
  else Vardefs vds

let mk_modifier (m : mod_kind) = Modifier m

let mk_aassign (lhs : form) (rhs : form) =
  Assign {aa_lhs=lhs; aa_rhs=rhs}

let mk_aoperation (name : string) (args : form list) =
  Operation {ao_name=name; ao_args=args}

let mk_lemma (name : string) (f : form) =
  Lemma {lemma_name = name; lemma_form = f}

let mk_invariant 
    (pub:publicness) 
    (enc:encapness) 
    (ensured:bool) 
    (name:string) 
    (f:form) : spec = 
  if (enc = EPlusVar) then
    failwith ("Invariant " ^ name ^ " declared with invalid encap+ modifier");
  Invariant  {
    inv_name = name;
    inv_public = (pub =PubPublic);
    inv_ensured = ensured;
    inv_encap = (enc=EncapVar);
    inv_form = f
  }

(** Get the formula associated with an invariant, along with a comment
    stating its name. *)
let good_looking_inv ?(msg = "") (inv : invariant_desc) : Form.form = 
  FormUtil.mk_comment ((if msg = "" then "" else ": ")
                       ^inv.inv_name) inv.inv_form

(** Add invariant's comment to the formula. *)
let add_comment (desc : invariant_desc) : invariant_desc =
  {desc with inv_form = mk_comment desc.inv_name desc.inv_form}
