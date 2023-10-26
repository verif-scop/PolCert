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

# Second-stage Makefile, after Coq extraction

# include Makefile.config

#
# Variables from Makefile.config:
# -OCAML_NATIVE_COMP: native-code compilation is supported
# -OCAML_OPT_COMP: can we use the natively-compiled compilers
# -COMPFLAGS: compile options
# -LINK_OPT: additional linker flags for the native binary
#

# Menhir configuration.

# include Makefile.menhir

#
# Variables from Makefile.menhir:
# -MENHIR_INCLUDES: additional menhir include paths
# -MENHIR_LIBS: additional menhir libraries
#

# Directories containing plain Caml code

ROOT_REL=../../

DIRS=. $(ROOT_REL)extraction \
  $(ROOT_REL)lib $(ROOT_REL)common $(ROOT_REL)$(ARCH) $(ROOT_REL)cfrontend $(ROOT_REL)cparser $(ROOT_REL)driver  $(shell find $(ROOT_REL)VPL/ocaml/src -type d ! -name extracted ! -name smt)


# DIRS_REL=()

# for string in "${DIRS[@]}"; do
#     new_string="$(ROOT_REL)$(string)"
#     DIRS_REL+=("$(new_string)")
# done

INCLUDES=$(patsubst %,-I %, $(DIRS))

# FIXME: move this to Makefile.config
include ../../Makefile.config

# Control of warnings:

WARNINGS=-w +a-4-8-9-26-27-29-32-33-34-37-39-40-42-44-50-66-69-70
extraction/%.cmx: WARNINGS +=-w -20-27-32..34-39-41-44..45-60-67
extraction/%.cmo: WARNINGS +=-w -20-27-32..34-39-41-44..45-60-67
# cparser/pre_parser.cmx: WARNINGS += -w -41
# cparser/pre_parser.cmo: WARNINGS += -w -41

COMPFLAGS+=-g -strict-sequence -safe-string -package zarith \
  $(INCLUDES) -I "$(MENHIR_DIR)" -I +str -I +unix -I +zarith \
  $(WARNINGS) $(WARN_ERRORS)


DOTOPT=

OCAMLC=ocamlfind ocamlc $(COMPFLAGS)
OCAMLOPT=ocamlfind ocamlopt $(COMPFLAGS)
OCAMLDEP=ocamldep$(DOTOPT) -slash $(INCLUDES)

OCAMLLEX=ocamllex -q
MODORDER=$(ROOT_REL)tools/modorder .depend.extr.test
COPY=cp

PARSERS=cparser/pre_parser.mly cparser/OpenScopParser.mly
LEXERS=cparser/Lexer.mll lib/Tokenize.mll \
	     lib/Readconfig.mll lib/Responsefile.mll lib/OpenScopLexer.mll \

# FIXME: menhirLib.cmxa or menhirLib.cmx
LIBS=str.cmxa unix.cmxa zarith.cmxa menhirLib.cmxa 
LIBS_BYTE=$(patsubst %.cmxa,%.cma,$(patsubst %.cmx,%.cmo,$(LIBS)))

EXECUTABLES=test
GENERATED=$(PARSERS:.mly=.mli) $(PARSERS:.mly=.ml) $(LEXERS:.mll=.ml)

# Beginning of part that assumes .depend.extr already exists

all:
	$(MAKE) clean
	$(MAKE) depend
	$(MAKE) test



ifeq ($(wildcard .depend.extr.test),.depend.extr.test)

CCOMP_OBJS:=$(shell $(MODORDER) ./test.cmx)

test: $(CCOMP_OBJS)
# @echo "Linking $@, $(CCOMP_OBJS)"
	@$(OCAMLOPT) -o $@ $(LIBS) $(LINK_OPT) $+
	@./test


include .depend.extr.test

endif

# End of part that assumes .depend.extr already exists

%.cmi: %.mli
# @echo "OCAMLC   $<"
	@$(OCAMLC) -c $<
%.cmo: %.ml
# @echo "OCAMLC   $<"
	@$(OCAMLC) -c $<
%.cmx: %.ml
# @echo "OCAMLOPT $<"
	@$(OCAMLOPT) -c $<

%.ml: %.mll
	$(OCAMLLEX) $<

clean:
	@rm -f $(EXECUTABLES)
	@rm -f .depend.extr.test
	@rm -f test.cmi test.cmt test.cmx test.o 
	@rm -f *.output *.pluto.c *.pluto.cloog *.stdout
	@rm -f .outfilename .regtile .srcfilename
	@rm -f orig.cpol orig.cpol
	@rm -f *.scop

# Generation of .depend.extr.test

depend:
# @echo "Analyzing OCaml dependencies"
	@$(OCAMLDEP) $(foreach d,$(DIRS),$(wildcard $(d)/*.ml)) $(GENERATED) >.depend.extr.test || { rm -f .depend.extr.test; exit 2; }
	@$(OCAMLDEP) $(foreach d,$(DIRS),$(wildcard $(d)/*.mli)) $(GENERATED) >>.depend.extr.test || { rm -f .depend.extr.test; exit 2; }
