# requires: coq 8.7

.PHONY: coq clean lscoqfiles cleanextract build install uninstall html

COQOPT ?= -opt

COQLIB := Vpl

COQ_FILES := CoqAddOn Debugging OptionMonad NumC \
	PositiveMapAddOn ProgVar LinTerm \
	Impure ImpureConfig DomainInterfaces \
	CstrC CstrLCF ConsSet PedraQBackend \
	PredTrans DomainGCL \
	Ring_polynom_AddOn ASTerm Itv ZNone ZNoneItv LinearizeBackend  \
        ASAtomicCond ASCond AssignD DomainFunctors \
	Ring_polynom_AddOnQ Qop CIndex Map_poly \
	PedraQ PedraZ \
	DemoPLVerifier DemoPLTests

V := $(addsuffix .v, $(COQ_FILES))
VO := $(addsuffix .vo, $(COQ_FILES))
# VIO := $(addsuffix .vio, $(COQ_FILES))
GLOB := $(addsuffix .glob, $(COQ_FILES))
DV := $(addsuffix .dv, $(COQ_FILES))

EXTRACT_FOLDER = ../ocaml/src/extracted
EXTRACT_TEST_FOLDER = ../test/coq_extracted

coq: $(VO)

DemoExtract.vo: $(VO) DemoExtract.v
	mkdir -p $(EXTRACT_FOLDER)
	cd $(EXTRACT_FOLDER) && (coqc $(COQOPT) -R ../../../coq/ $(COQLIB) ../../../coq/DemoExtract.v && rm -f ImpureConfig.mli)

DemoExtractTests.vo: DemoExtract.vo DemoPLTests.vo DemoExtractTests.v
	mkdir -p $(EXTRACT_TEST_FOLDER)
	cd $(EXTRACT_TEST_FOLDER) && coqc $(COQOPT) -R ../../coq/ $(COQLIB) ../../coq/DemoExtractTests.v && rm -f *.mli

%.vo: %.v
	coqc $(COQOPT)  -R . $(COQLIB) $<

# %.vio: %.v
# 	coqc -vio $(COQOPT)  -R . $(COQLIB) "$@"

%.dv: %.v
	coqdep -R . $(COQLIB) $< > $@

lscoqfiles:
	@echo ${V}

_CoqProject:
	@echo "-R . $(COQLIB)" > $@
	@echo "${V}" >> $@
	@echo "_CoqProject done..."

build.mk: _CoqProject
	coq_makefile -f _CoqProject -o build.mk

build: build.mk
	$(MAKE) -j -f build.mk "OPT:=-opt" all

html: build.mk
	$(MAKE) -j -f build.mk html

install: build.mk
	$(MAKE) -j -f build.mk "OPT:=-opt" install

uninstall: build.mk
	$(MAKE) -j -f build.mk "OPT:=-opt" uninstall || echo "skip last errors..."

clean:
	rm -rf *.vo *.dv *.glob *~ .*.aux html/

cleanextract:
	rm -rf DemoExtract.vo DemoExtractTests.vo $(EXTRACT_FOLDER) $(EXTRACT_TEST_FOLDER)

include $(DV)
