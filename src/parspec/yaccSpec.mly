%{
(** Parser for {!Specs} specifications, generated with ocamlyacc. *)
open Form
open FormUtil
open Specs

let parse_error = ParsingSpecAux.parse_error
%}

%token <string> STRING
%token <string> IDENT
%token <string> QIDENT
%token <int> NATLIT
%token COMMA SEMICOLON COLON COLONCOLON
%token LPAREN RPAREN
%token COLONEQUAL EQUAL EOF
%token LEMMA 
%token PUBLIC 
%token INVARIANT REQUIRES MODIFIES ENSURES 
%token SPECFIELD SPECSTATIC SPECVAR
%token PUBLIC PRIVATE STATIC GHOST ENCAP EPLUS ENSURED
%token CONSTDEFS VARDEFS 
%token READONLY CLAIMEDBY
%token PICKANY PICKWITNESS INDUCT WITNESS CONTRADICT FALSEINTRO MP INSTANTIATE PROOF
%token ASSERT NOTETHAT ASSUME SPLIT HAVOC FROM FOR OF
%token SUCHTHAT FORSUCH OVER WITH
%token SOME DISJOINT CASES SHOWEDCASE ASSUMING
%token HIDDEN

%start main             /* the entry point */
%type <Specs.spec list> main
%%

main: spec_list EOF {$1};

spec_list:
| spec oSEMICOLON spec_list {$1 :: $3}
| spec oSEMICOLON {[$1]}
;

spec:
| lemma {$1}
| invariant  {$1}
| contract   {$1}
| specvar {$1}
| constdefs  {$1}
| vardefs    {$1}
| modifier   {$1}
| assert_cmd {$1}
| noteThat_cmd {$1}
| assume_cmd {$1}
| pickAny_cmd {$1}
| pickWitness_cmd {$1}
| witness_cmd {$1}
| induct_cmd {$1}
| cases_cmd {$1}
| showedcase_cmd {$1}
| contradict_cmd {$1}
| falseintro_cmd {$1}
| instantiate_cmd {$1}
| mp_cmd {$1}
| proof_cmd {$1}
| assuming_cmd {$1}
| split_cmd {$1}
| havoc_cmd {$1}
| assign_cmd {$1}
| operation {$1}
;

SOMEopt:
| {false}
| SOME {true};

DISJOINTopt:
| {false}
| DISJOINT {true};  

assuming_cmd:
  ASSUMING cqform {Assuming $2};

induct_cmd:
  INDUCT cqform OVER qident COLONCOLON qtitem {mk_induct $2 ($4,$6)};

contradict_cmd:
  CONTRADICT cqform {Contradict $2};

falseintro_cmd:
  FALSEINTRO cqform {FalseIntro $2};

instantiate_cmd:
  INSTANTIATE cqform WITH qform_comma_list {mk_instantiate $2 $4};

mp_cmd:
  MP cqform {Mp $2};

proof_cmd:
  PROOF {Proof}

lemma:
  LEMMA IDENT COLON qform
  {mk_lemma $2 $4};

assert_cmd:
  ASSERT cqform fromClauseOpt
  {mk_assert $2 $3};

noteThat_cmd:
  NOTETHAT cqform fromClauseOpt forSuchOpt
  {mk_noteThat $2 $3 $4};

fromClauseOpt:
| {[]}
| fromClause {$1};

forSuchOpt:
| {[]}
| forSuch {$1};

forSuch:
  FORSUCH qident_list
  {$2};

fromClause:
  FROM qident_list
  {$2};

assume_cmd:
  ASSUME cqform 
  {Assume $2};

pickAny_cmd:
  PICKANY qtident_list suchThat_opt
  {mk_pickAny $2 $3};

pickWitness_cmd:
  PICKWITNESS qtident_list suchThat_opt
  {mk_pickWitness $2 $3};

witness_cmd:
  WITNESS qform_comma_list FOR cqform fromClauseOpt
  {mk_witness $2 $4 $5};

cases_cmd:
  CASES qform_comma_list FOR cqform fromClauseOpt
  {mk_cases $2 $4 $5};

showedcase_cmd:
  SHOWEDCASE NATLIT OF cqform fromClauseOpt
  {mk_showedcase $2 $4 $5};

suchThat_opt:
| {None}
| SUCHTHAT cqform {Some $2};

split_cmd:
  SPLIT cqform
  {Split $2};

havoc_cmd:
  HAVOC qform_comma_list suchThat_opt
  {mk_havoc $2 $3};

assign_cmd:
  qitem COLONEQUAL qform
  {mk_aassign $1 $3};

operation:
  IDENT LPAREN qform_comma_list RPAREN
  {mk_aoperation $1 $3};

optional_name:
| { "" }
| IDENT COLON { $1 }
| LPAREN STRING RPAREN { $2 }

ensuredness:
| {false}
| ENSURED {true}
;

invariant:
  publicness encapness ensuredness INVARIANT optional_name qform 
  { mk_invariant $1 $2 $3 $5 $6 };

contract:
  requires modifies ensures {mk_contract $1 $2 $3};

requires:
| { None }
| REQUIRES qform { Some $2 };

modifies:
| { None }
| MODIFIES qform_comma_list { Some $2 };

ensures:
  ENSURES qform {Some $2};

specvar:
  publicness encapness staticness ghostness SPECVAR IDENT COLONCOLON qtitem optinit
    {mk_specvar $1 $2 $3 $4 $6 $8 $9}

constdefs:
  publicness CONSTDEFS defs {mk_constdefs $1 $3};

vardefs:
    publicness VARDEFS defs
    { mk_vardefs $1 $3 };

defs:
| def oSEMICOLON { [$1] }
| defs def oSEMICOLON { $1 @ [$2] };

def: qform { mk_def $1 };

modifier:
| READONLY {mk_modifier Readonly}
| CLAIMEDBY IDENT {mk_modifier (ClaimedBy $2)}
| HIDDEN { mk_modifier Hidden }
| ENCAP {mk_modifier Encap}
| EPLUS {mk_modifier EPlus};

optinit:
| { None }
| EQUAL qitem { Some $2 };

qform_comma_list:
| qitem {[$1]}
| qform_comma_list COMMA qitem {$1 @ [$3]};
 
qitem:
| IDENT { mk_var $1 }
| qform { $1 };

cqform:
| qform {mk_annot_form "" $1}
| STRING COLON qform {mk_annot_form $1 $3}
| IDENT COLON qform {mk_annot_form $1 $3};

qform:
    STRING { ParseForm.parse_formula $1 };

qident:
  IDENT  {$1}
| QIDENT {$1};

qident_list:
  qident {[$1]}
| qident_list COMMA qident {$1 @ [$3]};

qtident_list:
  qident COLONCOLON qtitem {[($1,$3)]}
| qtident_list COMMA qident COLONCOLON qtitem {$1 @ [($3,$5)]};

qtitem:
| IDENT  { ParseForm.parse_type $1 }
| STRING { ParseForm.parse_type $1 };

publicness:
| PUBLIC  {PubPublic}
| PRIVATE {PubPrivate}
| {PubDefault};

staticness:
| STATIC {StatStatic}
| {StatInstance};

ghostness:
| GHOST {GhostVar}
| {NonGhostVar};

encapness:
| EPLUS {EPlusVar}
| ENCAP {EncapVar}
| {NonEncapVar};

oSEMICOLON:
| { () }
| SEMICOLON { () };
