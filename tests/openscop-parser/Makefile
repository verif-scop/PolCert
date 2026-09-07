.PHONY: test openscop-parser-regression

test:
	$(MAKE) -C ../.. -f Makefile.extr -f tests/openscop-parser/Makefile openscop-parser-regression

openscop-parser-regression: lib/OpenScopReader.cmx
	$(OCAMLOPT) -c tests/openscop-parser/test.ml
	$(OCAMLOPT) -o tests/openscop-parser/test $(LIBS) $(LINK_OPT) $(shell $(MODORDER) lib/OpenScopReader.cmx) tests/openscop-parser/test.cmx
	./tests/openscop-parser/test -conf polcert.ini
