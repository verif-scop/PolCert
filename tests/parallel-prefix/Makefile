PARALLEL_PREFIX_OBJS := $(shell $(MODORDER) extraction/Validator.cmx extraction/SPolIRs.cmx lib/OpenScopReader.cmx)

parallel-prefix-probe: $(PARALLEL_PREFIX_OBJS) tests/parallel-prefix/probe.cmx
	$(OCAMLOPT) -o tests/parallel-prefix/probe $(LIBS) $(LINK_OPT) $+
