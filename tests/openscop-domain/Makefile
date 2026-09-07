OPENSCOP_DOMAIN_OBJS := $(shell $(MODORDER) extraction/PolyLang.cmx extraction/SInstr.cmx)

.PHONY: test-openscop-domain
tests/openscop-domain/test.cmx: $(OPENSCOP_DOMAIN_OBJS)
test-openscop-domain: $(OPENSCOP_DOMAIN_OBJS) tests/openscop-domain/test.cmx
	$(OCAMLOPT) -o tests/openscop-domain/test $(LIBS) $(LINK_OPT) $+
	COMPCERT_CONFIG=tests/pluto/polcert.ini ./tests/openscop-domain/test
