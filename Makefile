#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the GNU Lesser General Public License as        #
#  published by the Free Software Foundation, either version 2.1 of   #
#  the License, or (at your option) any later version.                #
#  This file is also distributed under the terms of the               #
#  INRIA Non-Commercial License Agreement.                            #
#                                                                     #
#######################################################################

include Makefile.config
include VERSION

BUILDVERSION ?= $(version)
BUILDNR ?= $(buildnr)
TAG ?= $(tag)
BRANCH ?= $(branch)

ifeq ($(wildcard $(ARCH)_$(BITSIZE)),)
ARCHDIRS=$(ARCH)
else
ARCHDIRS=$(ARCH)_$(BITSIZE) $(ARCH)
endif

DIRS := lib common $(ARCHDIRS) cfrontend driver cparser src polygen samples syntax

COQINCLUDES := $(foreach d, $(DIRS), -R $(d) polcert.$(d))

ifeq ($(LIBRARY_FLOCQ),local)
DIRS += flocq/Core flocq/Prop flocq/Calc flocq/IEEE754
COQINCLUDES += -R flocq Flocq
endif

ifeq ($(LIBRARY_MENHIRLIB),local)
DIRS += MenhirLib
COQINCLUDES += -R MenhirLib MenhirLib
endif

ifeq ($(LIBRARY_VPL),local)
DIRS += VPL/coq
COQINCLUDES += -R VPL/coq Vpl
endif

# Notes on silenced Coq warnings:
#
# unused-pattern-matching-variable:
#    warning introduced in 8.13
#    the code rewrite that avoids the warning is not desirable
# deprecated-ident-entry:
#    warning introduced in 8.13
#    suggested change (use `name` instead of `ident`) supported since 8.13
# implicit-core-hint-db: inherit from PolyGen, to be solved upsteam
# deprecated-hint-without-locality: inherit from PolyGen, to be solved upsteam
# undeclared-scope: library file, to be solved
COQCOPTS ?= \
  -w -unused-pattern-matching-variable \
  -w -deprecated-ident-entry \
  -w -implicit-core-hint-db \
  -w -deprecated-hint-without-locality \
  -w -undeclared-scope

# deprecated-instance-without-locality:
#    warning introduced in 8.14
#    triggered by Menhir-generated files, to be solved upstream in Menhir
# cparser/Parser.vo: COQCOPTS += -w -deprecated-instance-without-locality

COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQDOC="$(COQBIN)coqdoc"
COQEXEC="$(COQBIN)coqtop" $(COQINCLUDES) -batch -load-vernac-source
COQCHK="$(COQBIN)coqchk" $(COQINCLUDES)
MENHIR=menhir
CP=cp

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq

ifeq ($(LIBRARY_FLOCQ),local)
FLOCQ=\
  Raux.v Zaux.v Defs.v Digits.v Float_prop.v FIX.v FLT.v FLX.v FTZ.v \
  Generic_fmt.v Round_pred.v Round_NE.v Ulp.v Core.v \
  Bracket.v Div.v Operations.v Plus.v Round.v Sqrt.v \
  Div_sqrt_error.v Mult_error.v Plus_error.v \
  Relative.v Sterbenz.v Round_odd.v Double_rounding.v \
  BinarySingleNaN.v Binary.v Bits.v
else
FLOCQ=
endif

# General-purpose libraries (in lib/)

VLIB=Axioms.v BoolEqual.v Coqlib.v Intv.v Maps.v \
  Zbits.v Integers.v Archi.v IEEE754_extra.v Floats.v \
  Decidableplus.v Misc.v ImpureOperations.v ImpureAlarmConfig.v \
  LibTactics.v Linalg.v LinalgExt.v Mymap.v sflib.v \
  TopoSort.v VplInterface.v Heuristics.v Ordered.v ListExt.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Linking.v \
  Events.v Globalenvs.v Memdata.v Memtype.v Memory.v \
  Values.v Smallstep.v Separation.v Builtins0.v Builtins1.v Builtins.v

# C front-end modules (in cfrontend/)

CFRONTEND=Ctypes.v Cop.v Csyntax.v Csem.v Ctyping.v Cstrategy.v Initializers.v Initializersproof.v

# TODO: May remove some files

BACKEND=
# Machregs.v Conventions1.v Locations.v Op.v

POLYGEN=ASTGen.v Canonizer.v CodeGen.v TyTy.v StateTy.v InstrTy.v Loop.v LoopGen.v \
  ParallelLoop.v \
  PolyLang.v PolyLoop.v PolyLoopSimpl.v PolyOperations.v PolyTest.v \
  Projection.v Result.v IterSemantics.v PolIRs.v CPolIRs.v TPolIRs.v InstanceListSema.v \
  LoopCleanup.v LoopSingletonCleanup.v LoopUnroll.v LoopStride.v

# Parser

PARSER=Cabs.v Parser.v

# MenhirLib

ifeq ($(LIBRARY_MENHIRLIB),local)
MENHIRLIB=Alphabet.v Automaton.v Grammar.v Interpreter_complete.v \
  Interpreter_correct.v Interpreter.v Main.v Validator_complete.v \
  Validator_safe.v Validator_classes.v
else
MENHIRLIB=
endif

# VPL (Verified Polyhedra Library)
ifeq ($(LIBRARY_VPL),local)
VPLLIB=ASAtomicCond.v ASCond.v AssignD.v ASTerm.v CIndex.v ConsSet.v \
  CoqAddOn.v CstrC.v CstrLCF.v Debugging.v DemoPLTests.v \
  DemoPLVerifier.v DomainFunctors.v DomainGCL.v DomainInterfaces.v \
  DomainGCL.v Impure.v ImpureConfig.v Itv.v LinearizeBackend.v LinTerm.v \
  Map_poly.v NumC.v OptionMonad.v PedraQ.v PedraQBackend.v PedraZ.v \
  PositiveMapAddOn.v PredTrans.v ProgVar.v Qop.v Ring_polynom_AddOn.v \
  Ring_polynom_AddOnQ.v ZNone.v ZNoneItv.v  
else
VPLLIB=
endif

# Source of PolCert

POLCERT_SRC = Base.v Convert.v \
  ExtractorFrontend.v ExtractorFacts.v ExtractorCorrect.v Extractor.v \
  PrepareCodegen.v StrengthenDomain.v \
  OpenScop.v OpenScopAST.v PolyBase.v PolyLang.v \
  SelectionSort.v StablePermut.v CState.v AffineValidator.v \
  ParallelValidator.v JamValidator.v LoopJamTrace.v LoopJamFusion.v LoopJamNative.v LoopJamValidator.v LoopJamLower.v LoopJamContext.v LoopJamBridge.v RawCodegenOrigin.v \
  ParallelCodegenCore.v ParallelCodegenCompatibility.v ParallelCodegenCorrect.v ParallelCodegen.v \
  PointWitness.v ISSWitness.v ISSRefinement.v \
  ISSBoolChecker.v ISSValidator.v ISSSemantics.v \
  ISSCutSemantics.v ISSValidatorCorrect.v \
  TilingWitness.v TilingList.v TilingRelation.v \
  TilingBoolChecker.v TilingValidator.v TilingBandScheduleValidator.v TilingBandMixedSecondValidator.v TilingBandPhaseScalarValidator.v TilingBandDirectRuntime.v \
  TilingCanonicalScheduleValidator.v Validator.v \
  CInstr.v TInstr.v CTy.v

# Putting everything together (in driver/)

DRIVER=PolOpt.v PolOptIdentityGenericISS.v PolOptCanonicalTiling.v PolOptBandTiling.v ParallelPolOpt.v ParallelPolOptCorrect.v PolOptCorrect.v VerifiedLoopPostpass.v VerifiedCompilerConfig.v VerifiedParallelCompilerConfig.v SBandTilingOptBridge.v SParallelPolOptBridge.v ExtractedPipelineCorrect.v PolOptPrepared.v CPolOpt.v TPolOpt.v TTilingCanonicalOpt.v TPolValidator.v

SAMPLES=CSample1.v CSample2.v CSample3.v CTypedLoopSamples.v ExtractorSmoke.v

SYNTAX_EXPERIMENT=SInstr.v SPolIRs.v SPolOptShared.v SPolOpt.v SParallelPolOptShared.v SParallelPolOpt.v SJamValidator.v SLoopJamValidator.v SLoopJamLower.v SLoopUnroll.v SLoopStride.v SLoopSymbolicSimpl.v STilingOpt.v STilingCanonicalOpt.v STilingBandSched.v SBandTilingOptShared.v SBandTilingOpt.v SVerifiedCompilerConfig.v SVerifiedParallelCompilerConfig.v SInstrSmoke.v

# Library for .v files generated by clightgen

# ifeq ($(CLIGHTGEN),true)
# EXPORTLIB=Ctypesdefs.v Clightdefs.v Csyntaxdefs.v
# else
# EXPORTLIB=
# endif

# All source files

FILES=$(VPLLIB) $(VLIB) $(COMMON) $(CFRONTEND) $(DRIVER) $(FLOCQ) \
  $(MENHIRLIB) $(POLYGEN) $(POLCERT_SRC) $(DRIVER) $(SAMPLES) \
  $(SYNTAX_EXPERIMENT)

# $(PARSER) $(BACKEND)
# Generated source files

# GENERATED = cparser/Parser.v VPL/ocaml/src/Wrapper.ml
GENERATED = VPL/ocaml/src/Wrapper.ml


all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) polcert
	$(MAKE) polopt

# $(MAKE) polcert # we don't compile the full polyhedral compiler now 

proof: $(FILES:.v=.vo)

# Turn off some warnings for Flocq and Menhirlib (& VPL)
# These warnings can only be addressed upstream

flocq/%.vo: COQCOPTS+=-w -deprecated-syntactic-definition
MenhirLib/%.vo: COQCOPTS+=-w -deprecated-syntactic-definition
VPL/%.vo: COQCOPTS+=-w -deprecated-syntactic-definition -w -deprecated-cutrewrite -w -fragile-hint-constr -w -implicit-core-hint-db -w -deprecated-hint-without-locality -w -deprecated-grab-existentials -w -notation-overridden -w -undeclared-scope -w -require-in-module -w -unused-intro-pattern -w -deprecated-focus -w -extraction-opaque-accessed

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v $(ARCH)/extractionMachdep.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	@if grep 'AXIOM TO BE REALIZED' extraction/*.ml; then \
            echo "An error occured during extraction to OCaml code."; \
            echo "Check the versions of Flocq and MenhirLib used."; \
            exit 2; \
         fi
	# Coq's modular extraction emits invalid aliases in these generated
	# signatures; infer the interfaces from the corresponding implementations.
	rm -f extraction/ImpureConfig.mli extraction/SParallelPolOpt.mli \
	      extraction/ParallelPolOpt.mli extraction/PolOptBandTiling.mli \
	      extraction/TilingBandScheduleValidator.mli \
	      extraction/TilingBandMixedSecondValidator.mli \
	      extraction/TilingBandPhaseScalarValidator.mli \
	      extraction/TilingBandDirectRuntime.mli \
	      extraction/STilingBandSched.mli \
	      extraction/SBandTilingOptShared.mli \
	      extraction/SParallelPolOptShared.mli extraction/SBandTilingOpt.mli
	touch extraction/STAMP

.depend.extr: extraction/STAMP tools/modorder driver/Version.ml
	$(MAKE) -f Makefile.extr depend

polcert: .depend.extr polcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr polcert

polopt: .depend.extr driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr polopt

GENERATED_SLOW_CASES=adi dct dsyr2k fdtd-1d fdtd-2d jacobi-1d-imper jacobi-2d-imper lu matmul-seq matmul-seq3 mxv-seq mxv-seq3 polynomial tce

FORCE:

.PHONY: proof extraction FORCE materialize-polopt-loop-suite test test-legacy-failure-gate test-legacy-failure-gate-unit test-polopt-loop-suite test-polopt-generated test-iss-pluto-suite test-iss-multicut-adversarial test-parallel-current-suite test-vector-current-suite test-extracted-zero-fallback test-typed-c-pipeline test-parallel-hint-mapping test-direct-only-tiling-routes test-non-second-level-tiling-routes test-scheduler-flag-forwarding test-second-level-tile-routes test-second-level-tile-rejection test-second-level-tile-manifest test-second-level-tile-suite test-pluto-compat-suite compare-rar-policy test-tiling-route-suites test-end-to-end-c-smoke test-end-to-end-c-correctness test-end-to-end-c-perf test-end-to-end-c-matmul-parallel test-end-to-end-c-matmul-vector test-end-to-end-generated-smoke test-end-to-end-generated-perf-default test-end-to-end-generated-perf test-end-to-end-generated-heavy test-end-to-end-generated test-end-to-end-generated-perf-parallel test-end-to-end-generated-slow-perf-parallel search-end-to-end-generated-best report-end-to-end-generated-best test-end-to-end-generated-perf-refresh tune-end-to-end-generated test-end-to-end-all test-pluto-bug-matmul-parallel-hint test-pluto-miscompilation-auto-affine-lp test-pluto-miscompilation-affine-fst test-pluto-miscompilation-tiling-innerpar test-pluto-diamond-nointratile-regression test-pluto-miscompilation-vanished-outer test-pluto-miscompilation-notile-unrolljam test-pluto-bugs test-diamond-tiling-suite unrolljam-effect-corpus artifact-check artifact-check-full artifact-capability-matrix proof-report profile-advect3d-codegen profile-advect3d-codegen-identity check-admitted test-open-proof-gate test-pluto-miscompilation-tiling-mixed-depth

test: .depend.extr polcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.test test --no-print-directory

test-legacy-failure-gate:
	bash tools/ci/check_legacy_failure_exit.sh

test-legacy-failure-gate-unit:
	bash tools/ci/check_legacy_failure_exit.sh --self-test

materialize-polopt-loop-suite: polopt
	rm -rf tests/polopt-generated/cases
	python3 tests/polopt-generated/tools/materialize_polopt_cases.py \
		--manifest tests/polopt-generated/materialize_manifest.json \
		--polopt ./polopt

test-polopt-loop-suite: materialize-polopt-loop-suite
	python3 tests/polopt-generated/tools/check_polopt_cases.py \
		--manifest tests/polopt-generated/strict_suite_manifest.json

test-polopt-generated: test-polopt-loop-suite

test-iss-pluto-suite: polopt polcert.ini test-iss-multicut-adversarial test-iss-native
	./polopt --validate-iss-pluto-suite

.PHONY: test-iss-lexer test-iss-native test-iss-adapter test-iss-periodic

test-iss-lexer:
	python3 -m unittest discover -s tools/iss -p 'test_*.py'

test-iss-native: polopt polcert.ini test-iss-lexer test-iss-adapter test-iss-periodic
	python3 tools/iss/run_native_iss_suite.py

test-iss-adapter: polopt polcert.ini
	python3 tools/iss/run_phase_iss_adapter_tests.py --source-root . \
		--output $$(mktemp -d /tmp/polcert-iss-adapter.XXXXXX)

test-iss-periodic: polopt polcert.ini
	python3 tools/iss/run_periodic_iss_suite.py --source-root . \
		--output $$(mktemp -d /tmp/polcert-iss-periodic.XXXXXX) \
		--require-retained \
		--kernels jacobi_1d_periodic_phase jacobi_2d_periodic_phase

test-iss-multicut-adversarial: polopt polcert.ini
	python3 tools/iss/run_iss_multicut_adversarial.py

test-iss-pluto-live-suite: polopt polcert.ini
	./polopt --validate-iss-pluto-live-suite

.PHONY: test-affine-integer-fastpath
test-affine-integer-fastpath: .depend.extr polcert.ini
	$(MAKE) -f Makefile.extr -f tests/affine-integer-fastpath/Makefile test-affine-integer-fastpath

.PHONY: test-parallel-scope
test-parallel-scope: .depend.extr polcert.ini
	$(MAKE) -f Makefile.extr -f tests/parallel-scope/Makefile test-parallel-scope

.PHONY: test-tiling-body-roundtrip
test-tiling-body-roundtrip: .depend.extr polcert.ini
	$(MAKE) -f Makefile.extr -f tests/parallel-scope/Makefile test-tiling-body-roundtrip

.PHONY: test-tiling-padding
test-tiling-padding: .depend.extr polcert.ini
	$(MAKE) -f Makefile.extr -f tests/parallel-scope/Makefile test-tiling-padding

.PHONY: test-openscop-domain
test-openscop-domain: .depend.extr polcert.ini
	$(MAKE) -f Makefile.extr -f tests/openscop-domain/Makefile test-openscop-domain

.PHONY: test-openscop-parser
test-openscop-parser: .depend.extr polcert.ini
	$(MAKE) -f Makefile.extr -f tests/openscop-parser/Makefile openscop-parser-regression

test-parallel-current-suite: polopt
	python3 tools/parallel_current/run_parallel_current_suite.py \
		--polopt ./polopt

test-vector-current-suite: polopt
	python3 tools/vector_current/run_vector_current_suite.py \
		--polopt ./polopt
	python3 -m unittest discover -s tools/vector_current -p 'test_*.py'
	python3 tools/vector_current/run_hinted_vector_suite.py --polopt ./polopt

test-extracted-zero-fallback: .depend.extr polcert.ini
	$(MAKE) -f Makefile.extr test-extracted-zero-fallback

test-typed-c-pipeline: .depend.extr polcert.ini
	$(MAKE) -f Makefile.extr test-typed-c-pipeline

test-parallel-hint-mapping: .depend.extr
	$(MAKE) -f Makefile.extr test-parallel-hint-mapping

.PHONY: test-phase-pipeline
test-phase-pipeline: .depend.extr
	$(MAKE) -f Makefile.extr -f tests/phase-pipeline/Makefile test-phase-pipeline

test-direct-only-tiling-routes: polopt polcert
	python3 tools/tiling_routes/check_complete_direct_routes.py \
		--polopt ./polopt \
		--polcert ./polcert

.PHONY: test-scalar-two-level-routes
test-scalar-two-level-routes: polopt
	python3 tools/tiling_routes/check_scalar_two_level_routes.py --source-root . \
		--output $$(mktemp -d /tmp/polcert-scalar-two-level.XXXXXX)/results

test-non-second-level-tiling-routes: polopt
	python3 tools/tiling_routes/check_non_second_level_routes.py \
		--polopt ./polopt

test-scheduler-flag-forwarding:
	python3 tools/second_level_tiling/check_scheduler_flag_forwarding.py

test-second-level-tile-routes: test-scheduler-flag-forwarding polopt
	python3 tools/second_level_tiling/run_second_level_tile_suite.py \
		--polopt ./polopt --part routes

test-second-level-tile-rejection: polopt polcert
	python3 tools/second_level_tiling/run_second_level_tile_suite.py \
		--polopt ./polopt --part rejection

test-second-level-general-schedule: polopt
	python3 tools/second_level_tiling/check_general_schedule_routes.py \
		--polopt ./polopt --output $$(mktemp -d /tmp/polcert-two-level-regression.XXXXXX)/results

test-second-level-tile-manifest: polopt
	python3 tools/second_level_tiling/run_second_level_tile_suite.py \
		--polopt ./polopt --part manifest

test-second-level-tile-suite: test-scheduler-flag-forwarding polopt polcert
	python3 tools/second_level_tiling/run_second_level_tile_suite.py \
		--polopt ./polopt

test-pluto-compat-suite: polopt
	python3 tools/polopt_flag_suites/run_pluto_compat_suite.py \
		--timeout 30

compare-rar-policy: polopt
	python3 tools/artifact/compare_rar_policy.py \
		--output /tmp/polcert-rar-policy.json

test-tiling-route-suites: test-direct-only-tiling-routes \
		test-non-second-level-tiling-routes \
		test-pluto-compat-suite \
		test-parallel-current-suite \
		test-vector-current-suite \
		test-second-level-tile-suite \
		test-diamond-tiling-suite

test-end-to-end-c-smoke: polopt
	python3 tools/end_to_end_c/run_suite.py \
		--polopt ./polopt \
		--exclude-suffix _perf \
		--benchmark-repeats 1

test-end-to-end-c-correctness: polopt
	python3 tools/end_to_end_c/run_suite.py \
		--polopt ./polopt \
		--exclude-suffix _perf \
		--benchmark-repeats 1 \
		--omp-threads 4
	python3 tools/end_to_end_c/run_case.py \
		tests/end-to-end-c/cases/matmul \
		--polopt ./polopt \
		--output-root tests/end-to-end-c/out-matmul-parallel \
		--polopt-arg=--parallel \
		--require-parallelized \
		--omp-threads 4 \
		--execution-repeats 3 \
		--benchmark-repeats 1
	python3 tools/end_to_end_c/run_case.py \
		tests/end-to-end-c/cases/matmul \
		--polopt ./polopt \
		--output-root tests/end-to-end-c/out-matmul-vector \
		--polopt-arg=--rar \
		--polopt-arg=--vector-current \
		--polopt-arg=5 \
		--require-vectorized \
		--benchmark-repeats 1

test-end-to-end-c-perf: polopt
	python3 tools/end_to_end_c/run_suite.py \
		--polopt ./polopt \
		--output-root tests/end-to-end-c/out-perf \
		--benchmark-repeats 3 \
		--name-suffix _perf

test-end-to-end-c-matmul-parallel: polopt
	python3 tools/end_to_end_c/run_case.py \
		tests/end-to-end-c/cases/matmul \
		--polopt ./polopt \
		--output-root tests/end-to-end-c/out-matmul-parallel \
		--polopt-arg=--parallel \
		--require-parallelized \
		--omp-threads 4 \
		--execution-repeats 3 \
		--benchmark-repeats 1

test-end-to-end-c-matmul-vector: polopt
	python3 tools/end_to_end_c/run_case.py \
		tests/end-to-end-c/cases/matmul \
		--polopt ./polopt \
		--output-root tests/end-to-end-c/out-matmul-vector \
		--polopt-arg=--rar \
		--polopt-arg=--vector-current \
		--polopt-arg=5 \
		--require-vectorized \
		--benchmark-repeats 1

test-end-to-end-generated-smoke: materialize-polopt-loop-suite
	python3 tools/end_to_end_c/run_generated_suite.py \
		--cases-root tests/polopt-generated/cases \
		--output-root tests/end-to-end-generated/out \
		--tier smoke \
		--benchmark-repeats 1

test-end-to-end-generated-perf-default: materialize-polopt-loop-suite
	python3 tools/end_to_end_c/run_generated_suite.py \
		--cases-root tests/polopt-generated/cases \
		--output-root tests/end-to-end-generated/out-perf \
		--tier perf \
		--benchmark-repeats 1

test-end-to-end-generated-perf: materialize-polopt-loop-suite
	python3 tools/end_to_end_c/run_generated_suite.py \
		--cases-root tests/polopt-generated/cases \
		--polopt ./polopt \
		--pipeline-config tests/end-to-end-generated/best_pipelines.json \
		--output-root tests/end-to-end-generated/out-perf-best \
		--tier perf \
		--benchmark-repeats 1

test-end-to-end-generated-heavy: materialize-polopt-loop-suite
	python3 tools/end_to_end_c/run_generated_suite.py \
		--cases-root tests/polopt-generated/cases \
		--output-root tests/end-to-end-generated/out-heavy \
		--tier heavy \
		--benchmark-repeats 1

test-end-to-end-generated-perf-parallel: materialize-polopt-loop-suite
	python3 tools/end_to_end_c/run_generated_suite.py \
		--cases-root tests/polopt-generated/cases \
		--polopt ./polopt \
		--polopt-arg=--parallel \
		--output-root tests/end-to-end-generated/out-perf-parallel \
		--tier perf \
		--omp-threads 4 \
		--benchmark-repeats 1

test-end-to-end-generated-slow-perf-parallel: materialize-polopt-loop-suite
	python3 tools/end_to_end_c/run_generated_suite.py \
		--cases-root tests/polopt-generated/cases \
		--polopt ./polopt \
		--polopt-arg=--parallel \
		--output-root tests/end-to-end-generated/out-perf-parallel-slow \
		--tier perf \
		--omp-threads 4 \
		--benchmark-repeats 1 \
		$(GENERATED_SLOW_CASES)

search-end-to-end-generated-best: materialize-polopt-loop-suite
	python3 tools/end_to_end_c/search_best_generated_pipelines.py \
		--cases-root tests/polopt-generated/cases \
		--polopt ./polopt \
		--pipeline-config tests/end-to-end-generated/pipeline_candidates.json \
		--output-root tests/end-to-end-generated/search \
		--summary-out tests/end-to-end-generated/best_pipelines.json \
		--report-out tests/end-to-end-generated/best_pipeline_report.json \
		--tier perf \
		--benchmark-repeats 1

report-end-to-end-generated-best:
	python3 tools/end_to_end_c/generate_best_pipeline_table.py \
		--summary-in tests/end-to-end-generated/best_pipelines.json \
		--report-in tests/end-to-end-generated/best_pipeline_report.json \
		--output tests/end-to-end-generated/BEST_PIPELINES.md

test-end-to-end-generated-perf-refresh: search-end-to-end-generated-best report-end-to-end-generated-best test-end-to-end-generated-perf

test-end-to-end-generated: test-end-to-end-generated-perf

tune-end-to-end-generated:
	python3 tools/end_to_end_c/tune_generated_params.py \
		--cases-root tests/polopt-generated/cases \
		--param-config tests/end-to-end-generated/param_tiers.json \
		--target-seconds 1.0 \
		--max-seconds 12.0 \
		--trial-timeout-seconds 8.0

test-end-to-end-all: test-end-to-end-c-smoke test-end-to-end-c-perf test-end-to-end-generated-perf

test-pluto-bug-matmul-parallel-hint: polopt polcert.ini
	python3 tools/pluto_bugs/run_matmul_parallel_hint.py

test-pluto-miscompilation-auto-affine-lp: polopt polcert.ini
	python3 tools/pluto_bugs/run_auto_affine_lp_cc_scaling.py

test-pluto-miscompilation-affine-fst: polopt polcert.ini
	python3 tools/pluto_bugs/run_affine_fst_reversed.py

test-pluto-miscompilation-tiling-innerpar: polopt polcert.ini
	python3 tools/pluto_bugs/run_tiling_innerpar_satvec.py

test-pluto-miscompilation-tiling-mixed-depth: polopt polcert.ini
	python3 tools/pluto_bugs/run_tiling_mixed_depth_cross_band.py

test-pluto-diamond-nointratile-regression: polopt polcert.ini
	python3 tools/pluto_bugs/run_diamond_nointratile_reschedule.py

test-pluto-miscompilation-vanished-outer: polopt polcert.ini
	python3 tools/pluto_bugs/run_vanished_outer_parallel.py

test-pluto-miscompilation-notile-unrolljam: polopt polcert.ini
	python3 tools/pluto_bugs/run_notile_unrolljam_nonpermutable.py

test-pluto-bugs: test-pluto-bug-matmul-parallel-hint test-pluto-miscompilation-auto-affine-lp test-pluto-miscompilation-affine-fst test-pluto-miscompilation-tiling-innerpar test-pluto-diamond-nointratile-regression test-pluto-miscompilation-vanished-outer test-pluto-miscompilation-notile-unrolljam test-pluto-miscompilation-tiling-mixed-depth
	python3 tools/pluto_bugs/test_innerpar_semantics.py

test-diamond-tiling-suite: polopt polcert
	python3 tools/diamond_tiling/run_pluto_diamond_suite.py

unrolljam-effect-corpus: polopt
	python3 tools/artifact/explore_unrolljam_effect_corpus.py \
		--output-root /tmp/polcert-unrolljam-effect-corpus

artifact-check: polopt polcert
	python3 tools/artifact/run_artifact_check.py --mode smoke

artifact-check-full: polopt polcert
	python3 tools/artifact/run_artifact_check.py --mode full

artifact-capability-matrix:
	python3 tools/artifact/generate_capability_matrix.py

proof-report:
	python3 tools/artifact/proof_report.py

profile-advect3d-codegen: polopt
	python3 tools/perf/run_stage_profile.py \
		--polopt ./polopt \
		--mode affine \
		tests/polopt-generated/inputs/advect3d.loop

profile-advect3d-codegen-identity: polopt
	python3 tools/perf/run_stage_profile.py \
		--polopt ./polopt \
		--mode identity \
		tests/polopt-generated/inputs/advect3d.loop

test-clean: 
	$(MAKE) -f Makefile.test clean

documentation: $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	./tools/coq2html -d doc/html/ -base polcert -short-names doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)
	cp -r doc/html/ /var/www/html

# Paper-oriented Rocq documentation.  Keep this set focused on the semantic
# spine; the generated declaration index links into the supporting modules.
PROOF_DOC_FILES = \
  src/CState.v src/CInstr.v polygen/InstanceListSema.v src/PolyLang.v \
  src/ExtractorFrontend.v src/ExtractorFacts.v src/ExtractorCorrect.v \
  src/ISSRefinement.v src/ISSBoolChecker.v src/ISSCutSemantics.v src/ISSValidatorCorrect.v \
  src/AffineValidator.v \
  src/TilingWitness.v src/TilingRelation.v src/TilingValidator.v src/TilingBandScheduleValidator.v \
  src/TilingBandMixedSecondValidator.v src/TilingBandPhaseScalarValidator.v \
  src/TilingBandDirectRuntime.v \
  polygen/ParallelLoop.v src/ParallelValidator.v src/RawCodegenOrigin.v \
  src/ParallelCodegenCore.v src/ParallelCodegenCompatibility.v src/ParallelCodegenCorrect.v \
  polygen/LoopUnroll.v driver/VerifiedLoopPostpass.v \
  src/PrepareCodegen.v src/StrengthenDomain.v \
  driver/PolOptCorrect.v driver/PolOptBandTiling.v driver/ParallelPolOptCorrect.v \
  driver/VerifiedCompilerConfig.v driver/VerifiedParallelCompilerConfig.v \
  syntax/SVerifiedCompilerConfig.v syntax/SVerifiedParallelCompilerConfig.v \
  driver/ExtractedPipelineCorrect.v

PROOF_DOC_OBJECTS = $(notdir $(PROOF_DOC_FILES:.v=.vo))
PROOF_DOC_GLOBS = $(addprefix doc/,$(notdir $(PROOF_DOC_FILES:.v=.glob)))

proof-documentation: $(PROOF_DOC_OBJECTS) doc/proof-index.html
	mkdir -p doc/proof-html
	rm -f doc/proof-html/*.html doc/proof-html/*.css
	cat $(PROOF_DOC_GLOBS) > doc/proof-html/proof.glob
	$(COQDOC) --html --toc --toc-depth 3 --index declarations \
	  --interpolate --utf8 --no-lib-name \
	  -t "PolCert proof reader" $(COQINCLUDES) \
	  -d doc/proof-html --glob-from doc/proof-html/proof.glob $(PROOF_DOC_FILES)
	cp doc/proof-index.html doc/proof-html/index.html
	python3 tools/docs/normalize_coqdoc_links.py doc/proof-html

.PHONY: proof-documentation

tools/ndfun: tools/ndfun.ml
ifeq ($(OCAML_NATIVE_COMP),true)
	ocamlopt -o tools/ndfun str.cmxa tools/ndfun.ml
else
	ocamlc -o tools/ndfun str.cma tools/ndfun.ml
endif

tools/modorder: tools/modorder.ml
ifeq ($(OCAML_NATIVE_COMP),true)
	ocamlopt -o tools/modorder str.cmxa tools/modorder.ml
else
	ocamlc -o tools/modorder str.cma tools/modorder.ml
endif


%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $<"
	@$(COQC) -dump-glob doc/$(*F).glob $<

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod a-w $*.v

polcert.ini: Makefile.config
	(echo "stdlib_path=$(LIBDIR)"; \
         echo "prepro=$(CPREPRO)"; \
         echo "linker=$(CLINKER)"; \
         echo "asm=$(CASM)"; \
	 echo "prepro_options=$(CPREPRO_OPTIONS)";\
	 echo "asm_options=$(CASM_OPTIONS)";\
	 echo "linker_options=$(CLINKER_OPTIONS)";\
         echo "arch=$(ARCH)"; \
         echo "model=$(MODEL)"; \
         echo "abi=$(ABI)"; \
         echo "endianness=$(ENDIANNESS)"; \
         echo "system=$(SYSTEM)"; \
         echo "has_runtime_lib=$(HAS_RUNTIME_LIB)"; \
         echo "has_standard_headers=$(HAS_STANDARD_HEADERS)"; \
         echo "asm_supports_cfi=$(ASM_SUPPORTS_CFI)"; \
	 echo "response_file_style=$(RESPONSEFILE)";) \
        > polcert.ini
# echo "scheduler=$(PLUTO)"; \
# echo "scheduler_options=$(PLUTO_OPTIONS);



# polcert.config: Makefile.config
# 	(echo "# CompCert configuration parameters"; \
#         echo "COMPCERT_ARCH=$(ARCH)"; \
#         echo "COMPCERT_MODEL=$(MODEL)"; \
#         echo "COMPCERT_ABI=$(ABI)"; \
#         echo "COMPCERT_ENDIANNESS=$(ENDIANNESS)"; \
#         echo "COMPCERT_BITSIZE=$(BITSIZE)"; \
#         echo "COMPCERT_SYSTEM=$(SYSTEM)"; \
#         echo "COMPCERT_VERSION=$(BUILDVERSION)"; \
#         echo "COMPCERT_BUILDNR=$(BUILDNR)"; \
#         echo "COMPCERT_TAG=$(TAG)"; \
#         echo "COMPCERT_BRANCH=$(BRANCH)" \
#         ) > compcert.config

driver/Version.ml: VERSION
	(echo 'let version = "$(BUILDVERSION)"'; \
         echo 'let buildnr = "$(BUILDNR)"'; \
         echo 'let tag = "$(TAG)"'; \
         echo 'let branch = "$(BRANCH)"') > driver/Version.ml

# cparser/Parser.v: cparser/Parser.vy
# 	@rm -f $@
# 	$(MENHIR) --coq --coq-no-version-check cparser/Parser.vy
# 	@chmod a-w $@

VPL/ocaml/src/Wrapper.ml: 
	cp -f VPL/ocaml/src/Wrapper_no_glpk.ml VPL/ocaml/src/Wrapper.ml

depend: $(GENERATED) depend1

depend1: $(FILES)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

install:
	install -d $(DESTDIR)$(BINDIR)
	install -m 0755 ./polcert $(DESTDIR)$(BINDIR)
	install -d $(DESTDIR)$(SHAREDIR)
	install -m 0644 ./polcert.ini $(DESTDIR)$(SHAREDIR)

clean:
	rm -f $(patsubst %, %/*.vo*, $(DIRS))
	rm -f $(patsubst %, %/.*.aux, $(DIRS))
	rm -rf doc/html doc/*.glob
	rm -f driver/Version.ml
	rm -f polcert.ini
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli .depend.extr
	rm -f tools/ndfun tools/modorder tools/*.cm? tools/*.o
	rm -f $(GENERATED) .depend
	rm -f .lia.cache
	rm -f result.txt
	$(MAKE) -f Makefile.extr clean
	$(MAKE) -f Makefile.test clean


camlclean:
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli 
	rm -f VPL/ocaml/src/extracted/*.ml VPL/ocaml/src/extracted/*.mli 
	rm -f .depend.extr 
	rm -f $(GENERATED) .depend
	$(MAKE) -f Makefile.extr clean


distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@python3 tools/ci/check_open_proofs.py $^

test-open-proof-gate:
	@python3 tools/ci/test_check_open_proofs.py

print-includes:
	@echo $(COQINCLUDES)

loc:
	cloc src --include-lang=Coq --force-lang=Coq,.v --by-file-by-lang

CoqProject:
	@echo $(COQINCLUDES) > _CoqProject

-include .depend

FORCE:
