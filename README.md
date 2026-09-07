# PolCert

PolCert is a verified polyhedral optimizer for loop fragments. It combines
verified extraction and code generation with verified validators for affine
scheduling, index-set splitting, tiling, and parallelization. Pluto supplies
optimization proposals; accepted results satisfy semantic refinement in the
formal loop language.

The implementation and proofs are written in Rocq (Coq). Extraction produces
two command-line tools:

- [`polopt`](POLOPT.md) optimizes a structured `.loop` program.
- [`polcert`](POLCERT.md) checks polyhedral transformation results supplied as
  OpenScop files.

## Getting started

Build the development environment and open a shell:

```sh
docker build --target development -t polcert-dev .
docker run --rm -it -v "$PWD":/polcert polcert-dev
```

Inside the container:

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
./polopt syntax/examples/matadd.loop
```

[ENVIRONMENT.md](ENVIRONMENT.md) describes the toolchain and clean builds.
The Docker image builds the fixed Pluto revision pinned in
[`tools/ci/pluto-baseline.env`](tools/ci/pluto-baseline.env). A separate
historical Pluto is used only by explicit bug-reproduction tests.

## Documentation

| Topic | Guide |
| --- | --- |
| Optimizer commands and options | [polopt](POLOPT.md) |
| Standalone validation | [polcert](POLCERT.md) |
| Input language | [Syntax](syntax/README.md) |
| Driver dispatch | [Flag guide](doc/POLOPT_FLAG_GUIDE.md) |
| Semantics and proof boundaries | [Verified pipeline](doc/VERIFIED_PIPELINE.md) |
| Proof structure and entry points | [Proof reading guide](doc/PROOF_READING_GUIDE.md) |
| Pluto exports and hint handling | [Pluto interface](doc/PLUTO_INTERFACE.md) |
| Regression tests and CI | [Testing](doc/TESTING.md) |
| Optimization retention and timing experiments | [Evaluation](doc/EVALUATION.md) |

## Scope

The generic formalization is parameterized by the instruction language and its
semantics. The executable frontend uses `SInstr`, a model for structured loop
fragments, rather than a full C compiler. Parsing, printing, and Pluto's search
are outside the verified core. Machine-integer overflow, realistic
floating-point behavior, and storage-changing transformations require further
semantic integration.

CI builds all proofs, checks for open proofs, rebuilds the extracted tools, and
runs correctness regressions. Full evaluation and performance measurements are
manual tasks; they do not run on every push or pull request.
