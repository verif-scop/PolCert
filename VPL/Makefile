all: vpl

vpl: setup
	$(MAKE) -C ocaml/

setup:
	cd ocaml; cp -f _oasis_no_glpk _oasis; cp -f src/Wrapper_no_glpk.ml src/Wrapper.ml; oasis setup

vpl_glpk: setup_glpk
	$(MAKE) -C ocaml/

setup_glpk:
	cd ocaml; cp -f _oasis_glpk _oasis; cp -f src/Wrapper_glpk.ml src/Wrapper.ml; oasis setup

clean:
	$(MAKE) -C ocaml/ clean
	$(MAKE) -C test/ clean
	rm -f ocaml/setup.data ocaml/setup.log

to_opam:
	cd ocaml
	oasis2opam --local

allclean: clean coq_clean test_clean oasis_clean

install:
	$(MAKE) -C ocaml/ install

uninstall:
	ocamlfind remove vpl

check:
	$(MAKE) -C test/ check

test_clean:
	$(MAKE) -C test/ clean

oasis_clean:
	$(RM) -f ocaml/Makefile ocaml/configure ocaml/_tags ocaml/myocamlbuild.ml ocaml/setup.ml ocaml/setup.data ocaml/setup.log
	$(RM) -f ocaml/src/META ocaml/src/*lib ocaml/src/*pack

# extract Coq files into the expected  ocaml/ subdir.
coq_update:
	$(MAKE) -j -C coq/ OPT:="-opt" DemoExtract.vo

coq_extract:
	$(MAKE) -C coq/ cleanextract
	$(MAKE) -j -C coq/ OPT:="-opt" DemoExtract.vo

# targets for opam installation.
coq_build:
	$(MAKE) -j -C coq/ OPT:="-opt" build

coq_install:
	$(MAKE) -C coq/ install

coq_uninstall:
	$(MAKE) -C coq/ uninstall

coq_clean:
	$(MAKE) -C coq clean

.PHONY: all vpl clean allclean install uninstall check coq_update coq_extract coq_build coq_install coq_uninstall coq_clean test_clean
