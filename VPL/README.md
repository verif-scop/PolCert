# VPL (Verified Polyhedra Library) version 0.2.1

## GENERAL INFORMATIONS

The VPL is an Ocaml library allowing to compute with convex polyhedra.
It provides standard operators -- certified in Coq -- to use this library as an abstract domain of polyhedra.

Contributors: Alexis Fouilhé, Alexandre Maréchal, Sylvain Boulmé, Hang Yu, Michaël Périn, David Monniaux.
Developed at Verimag and supported by ANR Verasco and ERC Stator.

If you find a bug or have any comment, feel free to contact us at verimag-polyhedra-developers@univ-grenoble-alpes.fr

## INSTALLATION

1. __From [opam](https://opam.ocaml.org/)__
	
    1. External Dependencies
	
        * [glpk](https://www.gnu.org/software/glpk/)
            __required version >= 4.61__

        * [eigen](http://eigen.tuxfamily.org/)
           (automatically installed by depexts on debian or ubuntu)
           _debian package libeigen3-dev_
           __tested with version 3.3.3__

    2. Installation
  
        First, add the following repository in your opam system:

            opam repo add vpl http://www-verimag.imag.fr/~boulme/opam-vpl

        Then, install the following packages (depending on your needs):

        * `vpl-core`: the ocaml library

          ```
                opam install vpl-core
          ```

        * `coq-vpl`: the Coq library (only needed to get Coq proofs about VPL operators)

          ```
	       opam install coq-vpl
          ```

        * `coq-vpltactic`: the [VplTactic](https://github.com/VERIMAG-Polyhedra/VplTactic) plugin for Coq (also install `coq-vpl` and `vpl-core`)

          ```
 	       opam install coq-vpltactic
          ```
          
      In case of trouble with this `opam` install, you should read [this](https://github.com/VERIMAG-Polyhedra/opam-vpl/blob/master/README.md#using-the-vpl-on-a-vagrantvirtualbox-virtual-machine).

2. __From sources__

    1. Dependencies

       The VPL requires the following packages:
	
       * [ocaml](http://caml.inria.fr/ocaml/index.en.html)
          __required version >= 4.02.3__
	
       * [zarith](https://forge.ocamlcore.org/projects/zarith)
          _available in OPAM_
          __tested with version 1.4.1__
          
       * [glpk](https://www.gnu.org/software/glpk/)
          __required version >= 4.61__

       * [eigen](http://eigen.tuxfamily.org/)
          _debian package libeigen3-dev_
          __tested with version 3.3.3__
	
       * [coq](https://coq.inria.fr/)
          (mandatory only if you want to re-extract files from Coq)
          _available in OPAM_
          __required version 8.7__ (use coq-vpl.0.2 for coq 8.6)

          __NB__ the `ocaml/src/extracted/` directory already contains extracted files from Coq.

    2. Compiling the VPL

       (Optional) To re-extract from the coq files, simply run at the root directory

            make coq_extract

       To compile the VPL, simply run from the root directory
	
            make vpl
	
       Tests can be run by typing

            make check

       Finally, to install the library with ocamlfind, type

            make install
	
       To uninstall the library from ocamlfind, run

            make uninstall


## Using the VPL

There are several ways to use the library.

* As an Ocaml library (opam package `vpl-core`),
the entry point is then the module UserInterface

* From Coq (opam package `coq-vpl`)

* As a Coq tactic (see [VplTactic](https://github.com/VERIMAG-Polyhedra/VplTactic))
