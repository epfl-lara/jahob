# for profiling:
# OCAMLC=ocamlcp -p f
export OCAMLC=ocamlc.opt
export OCAMLOPT=ocamlopt.opt
OCAMLDEP=ocamldep
OCAMLDOC=ocamldoc
OCAMLBROWSER=ocamlbrowser
DIRS=armci ast bapa decision form isabelle coq tptp \
     jast joust main mona parspec \
     unix-utils util vcgen smtlib bohne \
     speccomp
INCLUDES=-I armci -I ast -I bapa -I decision -I form -I isabelle -I coq \
	-I ../lib/xml-light \
	-I tptp -I jast -I joust -I main -I mona -I parspec -I presburger \
	-I unix-utils -I util -I vcgen -I smtlib -I bohne -I speccomp
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here
OCAMLYACC=ocamlyacc
OCAMLYACCFLAGS=
export OCAMLLEX=ocamllex
BIN=../bin
DOC=../doc
LIB=../lib
DOC_SRC=*/*.ml */*.mli
DEP_DOT_FILE=$(DOC)/depend/dependencies.dot
DEP_PS_FILE=$(DOC)/depend/dependencies.ps
DEP_PDF_FILE=$(DOC)/depend/dependencies.pdf

all: $(BIN)/formDecider.opt $(BIN)/bapa.opt $(BIN)/jpprint.opt \
	$(BIN)/jahob.opt \
	$(BIN)/timed_command \
#	$(BIN)/testmona.opt \
	$(BIN)/printShort.opt \
	$(BIN)/speccomp.opt

unix-utils/unix_util.o: unix-utils/unix_util.c
	$(OCAMLOPT) -c -cc "gcc" -ccopt "-fPIC -I`ocamlc -where`/caml \
	  -DPIC -DNATIVE_CODE -o unix-utils/unix_util.o"  $<

$(LIB)/xml-light/xml-light.cmxa: 
	make -C $(LIB)/xml-light xml-light.cmxa

COMMON_FILES=$(LIB)/xml-light/xml-light.cmxa \
	unix-utils/unix_util.o unix-utils/unixUtil.cmx \
	util/util.cmx util/debug.cmx \
	main/common.cmx main/cmdLine.cmx

# ------------------------------------------------------------
# form/
# ------------------------------------------------------------

form/yaccForm.output form/yaccForm.mli form/yaccForm.ml: form/yaccForm.mly
	$(OCAMLYACC) $(OCAMLYACCFLAGS) form/yaccForm.mly

form/lexForm.ml: form/lexForm.mll
	$(OCAMLLEX) form/lexForm.mll

FORM_FILES=form/form.cmx form/typeVars.cmx form/mlPrintForm.cmx		   \
	form/printForm.cmx form/formUtil.cmx form/parsingFormAux.cmx	   \
	form/yaccForm.cmx form/lexForm.cmx form/parseForm.cmx		   \
	form/typeReconstruct.cmx form/termRewrite.cmx coq/printFormCoq.cmx \
	form/folTranslation.cmx form/rtranclTranslation.cmx                \
	form/rtranclTreesTranslation.cmx form/pureListTranslation.cmx      \
	form/largeFormUtils.cmx

TESTFORM_FILES=$(COMMON_FILES) $(FORM_FILES) tptp/tptpPrettyPrinter.cmx form/testForm.cmx

$(BIN)/testForm.opt: $(TESTFORM_FILES)
	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) unix.cmxa str.cmxa $(TESTFORM_FILES)

# ------------------------------------------------------------
# isabelle/
# ------------------------------------------------------------

ISABELLE_FILES=isabelle/vclemmas.cmx isabelle/isabelle.cmx 

# ------------------------------------------------------------
# Coq/
# ------------------------------------------------------------

COQ_FILES=coq/coq.cmx 

# ------------------------------------------------------------
# TPTP/
# ------------------------------------------------------------

TPTP_FILES=tptp/assumpSort.cmx tptp/tptpPrettyPrinter.cmx tptp/spassPrettyPrinter.cmx

# ------------------------------------------------------------
# ast/
# ------------------------------------------------------------

TESTAST_FILES=$(COMMON_FILES) $(FORM_FILES) \
	ast/ast.cmx ast/astUtil.cmx $(ISABELLE_FILES) ast/resolveAst.cmx ast/printAst.cmx

$(BIN)/testAst.opt: $(TESTAST_FILES)
	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) unix.cmxa str.cmxa $(TESTAST_FILES)

# ------------------------------------------------------------
#                        DECISION PROCEDURES
# ------------------------------------------------------------

# ------------------------------------------------------------
# mona/
# ------------------------------------------------------------

MONA_FILES=mona/monaForm.cmx mona/monaPrint.cmx mona/monaUtil.cmx \
	mona/monaConvert.cmx mona/mona.cmx

TEST_MONA_FILES=$(FORM_FILES) $(MONA_FILES) mona/testMona.cmx

$(BIN)/testmona.opt: $(COMMON_FILES) $(TEST_MONA_FILES)
	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) unix.cmxa str.cmxa \
	$(COMMON_FILES) $(TEST_MONA_FILES)

# ------------------------------------------------------------
# presburger/
# ------------------------------------------------------------

# PRES_FILES=presburger/presburger.cmx

# $(BIN)/pres.opt: $(COMMON_FILES) $(PRES_FILES)
#	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) unix.cmxa str.cmxa \
#	$(COMMON_FILES) $(PRES_FILES)

# ------------------------------------------------------------
# simplify/
# ------------------------------------------------------------

# SIMPLIFY_FILES=simplify/simplify.cmx

# ------------------------------------------------------------
# bapa/
# ------------------------------------------------------------

BAPA_FILES= $(PRES_FILES) $(SMTLIB_FILES) \
        bapa/cardSetComp.cmx bapa/alpha.cmx bapa/formbapa.cmx \
	bapa/bapaform.cmx bapa/nlogn.cmx bapa/qfbapa.cmx bapa/bapa.cmx

# TEST_BAPA_FILES=$(FORM_FILES) $(BAPA_FILES) $(SIMPLIFY_FILES) bapa/testBapa.cmx

$(BIN)/bapa.opt: $(TEST_BAPA_FILES)
	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) unix.cmxa str.cmxa \
	$(COMMON_FILES) $(TEST_BAPA_FILES)

# ------------------------------------------------------------
# cbac (experimental)
# ------------------------------------------------------------

# CBAC_FILES=util/util.cmx bapa/gencbac.cmx

# $(BIN)/gencbac.opt: $(CBAC_FILES)
# 	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) unix.cmxa str.cmxa \
#	$(CBAC_FILES)

# ------------------------------------------------------------
# generate bapa formula/
# ------------------------------------------------------------

# GEN_BAPA_FILES=$(BAPA_FILES) bapa/genbapa.ml
# $(BIN)/genbapa.opt: $(FORM_FILES) $(GEN_BAPA_FILES)
# 	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) unix.cmxa str.cmxa \
#	$(COMMON_FILES) $(FORM_FILES) $(GEN_BAPA_FILES)


# ------------------------------------------------------------
# smtlib/
# ------------------------------------------------------------

SMTLIB_FILES=smtlib/smtPrint.cmx smtlib/smtTranslate.cmx \
	smtlib/smtCvcl.cmx smtlib/smt2Print.cmx smtlib/smt2Translate.cmx

# ------------------------------------------------------------
# type inference/
# ------------------------------------------------------------

# TYPE_INF_FILES=form/testInf.cmx

# $(BIN)/testinf.opt: $(COMMON_FILES) $(FORM_FILES) $(TYPE_INF_FILES)
# 	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) unix.cmxa str.cmxa \
#	$(COMMON_FILES) $(FORM_FILES) $(BAPA_FILES) $(TYPE_INF_FILES)

# ------------------------------------------------------------
# decision/
# ------------------------------------------------------------

DECISION_FILES=$(ISABELLE_FILES) $(COQ_FILES) $(MONA_FILES) \
	$(BAPA_FILES) $(SIMPLIFY_FILES) $(TPTP_FILES) \
        decision/slice.cmx decision/cardinality.cmx \
	decision/decider.cmx decision/idecider.cmx \
	decision/persistentCache.cmx decision/cachedDecider.cmx

$(BIN)/idecider.opt: $(FORM_FILES) $(DECISION_FILES)
	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) unix.cmxa str.cmxa \
	$(COMMON_FILES) $(DECISION_FILES)

$(BIN)/decider.opt: $(COMMON_FILES) $(FORM_FILES) \
	$(DECISION_FILES) decision/testDecider.cmx
	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) unix.cmxa str.cmxa \
	$(COMMON_FILES) $(FORM_FILES) $(DECISION_FILES) decision/testDecider.cmx

# ------------------------------------------------------------
#                        SYNTAX TREES
# ------------------------------------------------------------

# ------------------------------------------------------------
# joust/
# ------------------------------------------------------------

joust/parser.output joust/parser.mli joust/parser.ml: joust/parser.mly
	$(OCAMLYACC) $(OCAMLYACCFLAGS) joust/parser.mly

joust/lexer.ml: joust/lexer.mll
	$(OCAMLLEX) joust/lexer.mll

JOUST_FILES=joust/source.cmx \
	joust/syntax.cmx \
	joust/reserved.cmx \
	joust/pretty.cmx \
	joust/lexer.cmx \
	joust/parser.cmx

JPPRINT_FILES=$(JOUST_FILES) joust/comtest.cmx

$(BIN)/jpprint.opt: $(JPPRINT_FILES)
	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) unix.cmxa str.cmxa \
	$(JPPRINT_FILES)

# ------------------------------------------------------------
# parspec/
# ------------------------------------------------------------

parspec/yaccSpec.output parspec/yaccSpec.mli parspec/yaccSpec.ml: parspec/yaccSpec.mly
	$(OCAMLYACC) $(OCAMLYACCFLAGS) parspec/yaccSpec.mly

parspec/lexSpec.ml: parspec/lexSpec.mll
	$(OCAMLLEX) parspec/lexSpec.mll

PARSPEC_FILES=$(FORM_FILES) parspec/specs.cmx \
	parspec/parsingSpecAux.cmx parspec/yaccSpec.cmx parspec/lexSpec.cmx \
	parspec/parseSpec.cmx \
	jast/jtype.cmx jast/jast.cmx parspec/printSpec.cmx

# ------------------------------------------------------------
# bohne/
# ------------------------------------------------------------

$(LIB)/cudd/lib/libcudd.a: 
	make -C $(LIB)/cudd

$(LIB)/cudd/lib/libepd.a:
	make -C $(LIB)/cudd

bohne/caddie.o: bohne/caddie.c
	$(OCAMLOPT) -c -cc "gcc" -ccopt "-fPIC -I`ocamlc -where`/caml \
	  -I$(LIB)/cudd/include -DPIC -DNATIVE_CODE \
	  -o bohne/caddie.o"  $<

CCOPTS += -ccopt -L$(LIB)/cudd/lib -cclib -lcudd -cclib -lepd -cclib -lst -cclib -lmtr -cclib -lutil

BOHNE_FILES=$(LIB)/cudd/lib/libepd.a $(LIB)/cudd/lib/libcudd.a bohne/caddie.o bohne/caddieBdd.cmx \
	bohne/bf.cmx bohne/bf_set.cmx bohne/bohneUtil.cmx \
	bohne/bohneOptions.cmx bohne/bohnePred.cmx \
	bohne/bohneProgram.cmx bohne/bohneAbstraction.cmx \
	bohne/bohneRegion.cmx bohne/bohneRefine.cmx bohne/bohne.cmx \
	bohne/bohneDecaf.cmx bohne/bohneInterface.cmx


# ------------------------------------------------------------
# speccomp/
# ------------------------------------------------------------

speccomp/scParser.mli speccomp/scParser.ml: speccomp/scParser.mly
	$(OCAMLYACC) $(OCAMLYACCFLAGS) speccomp/scParser.mly

speccomp/scLexer.ml: speccomp/scLexer.mll
	$(OCAMLLEX) speccomp/scLexer.mll

SPECCOMP_FILES=speccomp/scTypes.cmx speccomp/scLexer.cmx	\
	speccomp/scParser.cmx speccomp/speccomp.cmx

# ------------------------------------------------------------
# main/
# ------------------------------------------------------------

JAHOB_FILES=$(COMMON_FILES) $(JOUST_FILES) $(PARSPEC_FILES) \
	ast/ast.cmx ast/astUtil.cmx jast/jastUtil.cmx \
	$(DECISION_FILES) \
	ast/resolveAst.cmx ast/printAst.cmx \
	jast/jastconsistency.cmx  \
	jast/jastjava.cmx jast/jast2ast.cmx jast/javajast.cmx \
	vcgen/background.cmx vcgen/sast.cmx \
	vcgen/encapsulation.cmx vcgen/static.cmx \
	vcgen/vcgen.cmx \
	vcgen/interpreter.cmx \
	vcgen/strongest_postcondition.cmx \
	vcgen/weakest_precondition.cmx \
	vcgen/loopInvariantInference.cmx \
	vcgen/symbolicExecution.cmx \
	vcgen/commute.cmx \
	armci/armcI.cmx \
	$(BOHNE_FILES) \
	main/analyze.cmx


$(BIN)/jahob.opt: $(JAHOB_FILES) main/jahob.cmx
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) unix.cmxa str.cmxa \
	$(JAHOB_FILES) main/jahob.cmx $(CCOPTS)

$(BIN)/formDecider.opt: $(JAHOB_FILES) main/formDecider.cmx
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) unix.cmxa str.cmxa \
	$(JAHOB_FILES) main/formDecider.cmx $(CCOPTS)

$(BIN)/assumptionRemovalTool.opt: $(JAHOB_FILES) main/assumptionRemovalTool.cmx
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) unix.cmxa str.cmxa \
	$(JAHOB_FILES)  main/assumptionRemovalTool.cmx $(CCOPTS)

$(BIN)/tptpConverter.opt: $(JAHOB_FILES) main/tptpConverter.cmx
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) unix.cmxa str.cmxa \
	$(JAHOB_FILES)  main/tptpConverter.cmx $(CCOPTS)

$(BIN)/printShort.opt: $(JAHOB_FILES) main/printShort.cmx
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) unix.cmxa str.cmxa \
	$(JAHOB_FILES) main/printShort.cmx $(CCOPTS)

$(BIN)/bohne.opt: $(JAHOB_FILES) bohne/bohneExec.cmx
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) unix.cmxa str.cmxa \
	$(JAHOB_FILES) bohne/bohneExec.cmx $(CCOPTS)

$(BIN)/speccomp.opt: $(SPECCOMP_FILES)
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) \
	$(SPECCOMP_FILES) $(CCOPTS)

# ------------------------------------------------------------
# $(BIN)/timed_command
# ------------------------------------------------------------

$(BIN)/timed_command: unix-utils/timed_command.c
	gcc -o $(BIN)/timed_command unix-utils/timed_command.c

# ------------------------------------------------------------
# html documentation
# ------------------------------------------------------------

doc: $(DOC_SRC)
	$(OCAMLDOC) -t "Jahob Documentation" -html -sort -keep-code \
	 -d $(DOC)/html $(INCLUDES) */*.ml */*.mli

docdep:
	$(OCAMLDOC) -dot -t "Jahob Dependencies" -o $(DEP_DOT_FILE) $(INCLUDES) \
		-dot-reduce */*.ml */*.mli; \
	dot -Tps -o $(DEP_PS_FILE) $(DEP_DOT_FILE); \
	ps2pdf $(DEP_PS_FILE) $(DEP_PDF_FILE)

docmanual:
	cd ../doc/manual; \
	./l

# ------------------------------------------------------------
# Interface and implementation browsing
# ------------------------------------------------------------

browse:
	 $(OCAMLBROWSER) $(INCLUDES)

# ------------------------------------------------------------
# Common rules
# ------------------------------------------------------------
.SUFFIXES: .ml .mli .cmx .cmi .cmx .mly .mll

.ml.annot:
	$(OCAMLC) $(OCAMLFLAGS) -c -g $<

.mli.cmi:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

# Clean up
cleanast:
	cd ast; \
	rm -f *.cm[iox] *.o *.annot

cleanarmci:
	cd armci; \
	rm -f *.cm[iox] *.o *.annot

cleanbapa:
	cd bapa; \
	rm -f *.cm[iox] *.o *.annot

cleancoq:
	cd coq; \
	rm -f *.cm[iox] *.o *.annot

cleandecision:
	cd decision; \
	rm -f *.cm[iox] *.o *.annot


cleanform:
	rm -f $(BIN)/testForm; \
	cd form; \
	rm -f *.cm[iox] *.o *.annot \
	rm -f yaccForm.ml yaccForm.mli lexForm.ml

cleanmona:
	rm -f $(BIN)/testmona; \
	cd mona; \
	rm -f *.cm[iox] *.o *.annot \

cleanparspec:
	cd parspec; \
	rm -f *.cm[iox] *.o *.annot \
	rm -f yaccSpec.ml yaccSpec.mli lexSpec.ml

cleanjast:
	cd jast; \
	rm -f *.cm[iox] *.o *.annot

cleanjoust:
	cd joust; \
	rm -f *.cm[iox] *.o *.annot \
	rm -f parser.ml parser.mli lexer.ml

cleanmain:
	cd main; \
	rm -f *.cm[iox] *.o *.annot

cleanpres:
	cd presburger; \
	rm -f *.cm[iox] *.o *.annot

cleanutil:
	cd util; \
	rm -f *.cm[iox] *.o *.annot; \
	cd ..; \
        cd $(LIB)/xml-light; \
	make clean

cleanvcgen:
	cd vcgen; \
	rm -f *.cm[iox] *.o *.annot

cleansimplify:
	cd simplify; \
	rm -f *.cm[iox] *.o *.annot

cleansmtlib:
	cd smtlib; \
	rm -f *.cm[iox] *.o *.annot

cleanisabelle:
	cd isabelle; \
	rm -f *.cm[iox] *.o *.annot

cleanbohne:
	cd bohne; \
	rm -f *.cm[iox] *.o *.annot; \
	cd ..; \
	cd $(LIB)/cudd; \
	make distclean

cleantptp:
	cd tptp; \
	rm -f *.cm[iox] *.o *.annot

cleanspeccomp:
	cd speccomp; \
	rm -f *.cm[iox] *.o *.annot; \
	rm -f scParser.ml scParser.mli scLexer.ml

cleanunixutils:
	cd unix-utils; \
	rm -f *.cm[iox] *.o *.annot; \

clean: cleanast cleanarmci cleanbapa cleancoq cleandecision cleanform \
	cleanparspec \
	cleanjast cleanjoust cleanmona cleanpres cleanutil cleanvcgen \
	cleanmain cleanisabelle cleansimplify cleansmtlib cleanbohne \
	cleantptp cleanspeccomp cleanunixutils

# Dependencies
beforedepend: form/yaccForm.mli form/yaccForm.ml form/lexForm.ml	 \
	parspec/yaccSpec.mli parspec/yaccSpec.ml parspec/lexSpec.ml	 \
	joust/parser.mli joust/parser.ml joust/lexer.ml                  \
	speccomp/scLexer.ml speccomp/scParser.ml                         \
	ast/printAst.mli                                                 \
	vcgen/symbolicExecution.mli vcgen/commute.mli

depend: beforedepend
	(for d in $(DIRS); \
	do $(OCAMLDEP) $(INCLUDES) -native $$d/*.mli $$d/*.ml; \
	done) > .depend.opt

-include .depend.opt
