# Development Environment

The [Dockerfile](Dockerfile) defines the reference build environment. It pins
OCaml 4.13.1, Coq 8.13.2, and the OCaml libraries, and rebuilds both Pluto
revisions listed in [tools/ci/pluto-baseline.env](tools/ci/pluto-baseline.env).
The historical compiler is isolated at `/opt/polcert/pluto-buggy`; ordinary
optimization uses `/pluto`.

## Interactive Development

```sh
docker build --target development -t polcert-dev .
docker run --rm -it -v "$PWD":/polcert polcert-dev
```

The bind mount makes edits and build outputs visible in the host checkout.
It also hides the image's source directory, so a new checkout still needs
the build below. Image construction requires network access for the base image,
system packages, opam packages, and pinned Pluto sources.
After mounting a fresh checkout, configure it before building:

```sh
eval "$(opam env --switch=polcert)"
./configure x86_64-linux
make depend
make -j2 proof
make -s check-admitted
make extraction
make polcert.ini
make polcert
make polopt
```

For a clean rebuild, run `make clean` before `make depend`. Large proof modules
use several GiB of memory; start with two proof jobs. The CI scripts choose
proof and OCaml build parallelism separately according to available memory.

After changes to Rocq sources, run `make depend`, rebuild the affected proofs,
and repeat extraction and both executable builds. Old binaries do not reflect
new proofs until extraction and linking finish. Run the relevant
[regressions](doc/TESTING.md) before using the result in an experiment.

## CI-Equivalent Validation

Build the source and run the isolated regression shards:

```sh
docker build --target ci -t polcert-ci .
bash tools/ci/run_ci_shards.sh polcert-ci
```

The `ci` target runs the baseline checks, a clean proof build, the open-proof
gate, extraction, and executable builds. The shard runner then tests those
executables in separate containers. Logs identify each check and its exit
status. See [Testing](doc/TESTING.md) for smaller test selections.

## Native Setup

Install the system and opam dependencies listed in the Dockerfile, including
GLPK, GMP, Eigen, and the pinned Coq/OCaml versions. Build the pinned fixed
[Pluto fork](https://github.com/verif-scop/pluto), with its submodules initialized
and GLPK enabled. `POLCERT_PLUTO` selects the optimizer used by the driver;
test and Evaluation runners have their own producer options, including
`--pluto` and `--polycc`. Check the runner's `--help` when using native paths.
Historical bug tests additionally need
the pinned `buggy` checkout and `POLCERT_BUGGY_ROOT`.

`make documentation` also requires the Python Markdown package
(`python3-markdown` on Ubuntu). It generates browsable guides and Rocq source
pages under `doc/proof-html/`; open `index.html` in a browser.

Use the same configure and build commands as above. A successful native build
does not establish that it used the pinned CI dependencies; retain the
toolchain and compiler revisions with any reported measurements.
