PHASE_PIPELINE_OBJS := $(shell $(MODORDER) driver/Scheduler.cmx syntax/SLoopCli.cmx)

.PHONY: test-phase-pipeline
tests/phase-pipeline/test.cmx: $(PHASE_PIPELINE_OBJS)
test-phase-pipeline: $(PHASE_PIPELINE_OBJS) tests/phase-pipeline/test.cmx
	$(OCAMLOPT) -o tests/phase-pipeline/test $(LIBS) $(LINK_OPT) $+
	COMPCERT_CONFIG=tests/pluto/polcert.ini ./tests/phase-pipeline/test
