.PHONY: test-affine-integer-fastpath
test-affine-integer-fastpath:
	$(OCAMLOPT) -o tests/affine-integer-fastpath/test $(LIBS) $(LINK_OPT) $(shell $(MODORDER) extraction/AffineValidator.cmx extraction/SPolIRs.cmx lib/Camlcoq.cmx) tests/affine-integer-fastpath/test.ml
	COMPCERT_CONFIG=tests/pluto/polcert.ini tests/affine-integer-fastpath/test
