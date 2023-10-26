#!/bin/bash

OCAMLFIND=ocamlfind
VPLPATH=$($OCAMLFIND query vpl)

ocaml -I $VPLPATH $1
