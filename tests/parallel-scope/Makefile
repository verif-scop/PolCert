PARALLEL_SCOPE_OBJS := $(shell $(MODORDER) extraction/SParallelPolOpt.cmx)

.PHONY: test-parallel-scope
tests/parallel-scope/test.cmx: $(PARALLEL_SCOPE_OBJS)
test-parallel-scope: $(PARALLEL_SCOPE_OBJS) tests/parallel-scope/test.cmx
	$(OCAMLOPT) -o tests/parallel-scope/test $(LIBS) $(LINK_OPT) $+
	COMPCERT_CONFIG=tests/pluto/polcert.ini ./tests/parallel-scope/test

.PHONY: test-tiling-body-roundtrip
tests/parallel-scope/body_roundtrip_test.cmx: $(PARALLEL_SCOPE_OBJS)
test-tiling-body-roundtrip: $(PARALLEL_SCOPE_OBJS) tests/parallel-scope/body_roundtrip_test.cmx
	$(OCAMLOPT) -o tests/parallel-scope/body_roundtrip_test $(LIBS) $(LINK_OPT) $+
	COMPCERT_CONFIG=tests/pluto/polcert.ini ./tests/parallel-scope/body_roundtrip_test

TILING_PADDING_OBJS := $(shell $(MODORDER) extraction/SPolOpt.cmx extraction/SParallelPolOpt.cmx extraction/STilingBandSched.cmx syntax/SLoopElab.cmx syntax/SLoopParse.cmx driver/PhaseTiling.cmx)

.PHONY: test-tiling-padding
tests/parallel-scope/tiling_padding_test.cmx: $(TILING_PADDING_OBJS)
test-tiling-padding: $(TILING_PADDING_OBJS) tests/parallel-scope/tiling_padding_test.cmx
	$(OCAMLOPT) -o tests/parallel-scope/tiling_padding_test $(LIBS) $(LINK_OPT) $+
	COMPCERT_CONFIG=tests/pluto/polcert.ini ./tests/parallel-scope/tiling_padding_test
