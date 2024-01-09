# PolCert: Verified Validation for Affine Polyhedral Scheduling

This repository contains mechanized proof of "Verified Validation for Affine Polyhedral Scheduling" in the Coq proof assistent. It contains a general verified validation framework (PolCert), and its verified instantiation of a [CompCert](https://github.com/AbsInt/CompCert) instruction's variant (CInstr). The algorithm's completeness is evaluated with [the Pluto compiler](https://github.com/bondhugula/pluto).

Paper of this machanization will come out soon.

**Acknowledgement**: This project bases on [Verified Polyhedra Library (VPL)](https://github.com/VERIMAG-Polyhedra/VPL) and [PolyGen](https://github.com/Ekdohibs/PolyGen), and similar idea can be found at [s2sloop](https://github.com/pilki/s2sLoop).

## Overview

The validator takes two polyhedral models (before and after auto-transformation like pluto's core algorithm), and output their equivalence (equal or unknown). It can only deal with two polyhedron models with strictly equal instructions, differing only in schedule (scattering) functions (then only supports reordering of instances, not supporting tiling etc). The validation algorithm just constructs test polyhedrons for all WAW/WAR/RAW dependences (write/read access functions should be given) for their violation.

Users should instantiate their own [Instr](./polygen/InstrTy.v), which merely demands the language's semantics implies permutability under [Bernstein’s Conditions](https://link.springer.com/referenceworkentry/10.1007/978-0-387-09766-4_521); this needs users to provide a verified checker function (like, basing on symbolic execution) for validity of read and write access functions regarding to the semantics. As an example, we provide CompCert's instruction (called [CInstr](./src/CInstr.v)) as its instantiation and parameterize the validator (see [CPolOpt.v](./driver/CPolOpt.v)). Note that, we wrap the Pluto compiler with the validator to achieve verified compilation. Nevertheless, there's still several challenges to (seamlessly) integrate polyhedral compilation into CompCert as an extension, like machanizing a verified extractor, dealing with assumptions (heavy static reasoning) of polyhedal compilation ([optimistic approach](https://dl.acm.org/doi/10.5555/3049832.3049864) seems possible, but at least need to change CompCert's semantics for overflow flag (see [this report](https://inria.hal.science/hal-00655485/file/polyproofs.pdf))), more complete scheduling supports, vectorization and parallemism... Also, we find PolyGen (see [this issue](https://github.com/Ekdohibs/PolyGen/issues/1)) need extra constraints to restrict the length of iteration vector (i.e., *depth*), which is not convenient and is not compatible to, like, Pluto's output format; we introduce additional field *depth* in the polyhedral model to simplify this, but this leads to a (small) semantics gap. Some efforts are needed to reuse PolyGen's proof, though it is now compiled together with ours. 

An executable `polcert` can be extracted and runs on two polyhedron models in [OpenScop format](https://github.com/periscop/openscop) (of course, there's conversion between OpenScop and our inner representation). Though, as Openscop format does not contain information like typing and can be complex eough, we can not give it valid semantics (like [CInstr](./src/CInstr.v)). Only the algorithms are reused. Access function's consistency to instruction's semantics is then lifted as assumption. With these in mind, the algorithm is tested on pluto's 62 test cases. See [TInstr](./src/TInstr.v) and [TPolValidator](./driver/TPolValidator.v) for this trivial instantiation. 

## Structure

Main proofs can be found in [`./src`](./src) folder. Unit tests are in [`./tests`](./tests) folder; [`./tests/pluto-all`](./tests/pluto-all) includes all 62 test cases evaluated with Pluto. 

For more complete project information, see [documentation](#documentation).

<details><summary>(click to expand) <strong>Project structure</strong></summary>


```
.
├── Dockerfile, Makefile[...], configure
├── README.md
├── doc                # Chore: for documentation 
├── src                # Coq: main machanization of this project
├── VPL                # Coq: Verified Polyhedra Library
├── polygen            # Coq: PolyGen's machanization
├── flocq              # Coq: Floating point Library, used by CompCert
├── cfrontend, common, lib, x86, x86_64  # Coq: (mainly) CompCert Coq files
├── tests              # Chore: test suit and test scripts
├── cparser, driver    # OCaml: compiler driver, amended from CompCert's
├── extraction         # Chore: for coq file's ocaml extraction 
├── samples            # Coq: sample polyhedral programs (instantiate with CInstr) 
├── tools              # Chore: just some tools
└── MenhirLib          # TBD: the verified parser, may reuse it later, now useless
```


</details>


## Usage

### Build (Docker)

We recommand you to test our implementation with docker. You can build the docker image from scatch with (see [Dockerfile](./Dockerfile)):

```
# this may take (less-than) 30 minutes, depend on your network condition
docker build . -t polcert
```

You can also fetch the offical image (may not be updated in time, but it should work) from [the provided docker-hub repository](https://hub.docker.com/repository/docker/hughshine/polcert/) by:

```
docker pull hughshine/polcert:latest
```

Then you can run the project inside the docker:

```
sudo docker run -p 80:80 -ti [--rm] [hughshine/]polcert:latest
```

Inside the docker container, try the following command to build the project:

```
make -j4  # compile coq proofs and extract an executable
make install  # install the executable to PATH, invoke with 'polcert <pol1> <pol2>'
make test # runs all unit tests & evaluation on pluto (output file `result.txt`)
# cat result.txt
## Test (just test name) ToP (time of pluto's auto-transformation, ms) ToB (time of backward refinement validation, ms) ToF (time of forward refinement validation, ms) Result (EQ/LT/GT/NE)
## covcol 4.12 366.14 294.55 EQ
## dsyr2k 2.96 103.09 79.98 EQ
## ...
# make clean && make camlclean # if your project break
```

You can run `make check-admitted` for unfinished proofs. No additional axioms are introduced (you have to manually check this). You can count lines of code of Coq with [cloc](https://github.com/AlDanial/cloc) with `make loc` (note that the satistics is not complete, but roughly accurate; we added some code to library files).

For the docker image, it bases on [prebuild pluto base image](https://hub.docker.com/repository/docker/hughshine/pluto-verif) (we modify pluto to dump its intermediate representation), installs coq/ocaml environment (and some tools), and prepares the configuration. See the [Dockerfile](./Dockerfile) for more details. If you want to install the project manually, just follow the steps in [Dockerfile](./Dockerfile).

### Documentation

You can generate project's full documentation by `make documentation` (After running `make`) and view it at [localhost](http://localhost/) (If you use the docker image).

### Try your own test case

If your build and installation succeeds, there should be executable `polcert` in your PATH. `pluto` (see [here](https://github.com/verif-scop/pluto)) is already in your path. Now you can write your own test case (`vim` is provided in the image) like `test.c`,

```
#pragma scop
// Your loop should be surrounded with pragma
// You don't need to write complete c program, as pluto intercepts the fragment
#pragma endscop
```

and then invoke `pluto` with 

```
pluto --dumpscop --nointratileopt --nodiamond-tile --noprevector \
      --smartfuse --nounrolljam --noparallel --notile --rar test.c
```

If compilation succeeds, intermediate files (see [OpenScop format](https://github.com/periscop/openscop)) are generated:

```
ls *.scop
# test.afterscheduling.scop
# test.beforescheduling.scop
```

The run `polcert <pol1> <pol2>` on them. Note that `polcert` tries to run the validation algorithm twice, so any order is ok.

```
polcert test.beforescheduling.scop test.afterscheduling.scop
```

It will give output like:

```
[EQ] The two polyhedral models (test.beforescheduling.scop, test.afterscheduling.scop) are equivalent.
# or
[GT] Polyhedral model test.beforescheduling.scop refines test.afterscheduling.scop.
# or
[LT] Polyhedral model test.afterscheduling.scop refines test.beforescheduling.scop.
# or
[NE] Cannot determine refinement relations between the two polyhedral models (test.afterscheduling.scop, test.beforescheduling.scop).
```

--- 

## Note: Warning Suppression

We turn off several warnings for clarity. Three additional (and unimportant) Coq warnings were turned off comparing to CompCert. OCaml's warnings are not discussed as they do not affect formal guarantees (most of them come from extracted VPL code).

**Coq compilation (see [Makefile](./Makefile)):**
1. `-unused-pattern-matching-variable`: disabled in CompCert
2. `-deprecated-ident-entry`: disabled in CompCert
3. `-implicit-core-hint-db`: inherit from PolyGen, to be solved upsteam
4. `-deprecated-hint-without-locality`: inherit from PolyGen, to be solved upsteam
5. `-undeclared-scope`: library file, to be solved

**Coq extraction (see [extraction.v](./extraction/extraction.v)):**
1. `-extraction-ambiguous-name`, does not matter
2. `-extraction-opaque-accessed`, to be fixed in VPL

**Ocaml compilation (see [Makefile.extr](./Makefile.extr)).**


## LICENSE

See [LICENSE](./LICENSE). We follow [PolyGen](https://github.com/Ekdohibs/PolyGen).
