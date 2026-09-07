# PolCert

PolCert is a verified polyhedral optimizer for loop fragments. It uses Pluto
to propose optimizations and verified validators to check them. Loop extraction,
code generation, and supporting transformations are verified in Rocq (Coq).
The compiler supports affine scheduling, index-set splitting, rectangular and
diamond tiling, two-level tiling, and parallelization.

## Build and Run

Build the development image and open the checkout inside it:

```sh
docker build --target development -t polcert-dev .
docker run --rm -it -v "$PWD":/polcert polcert-dev
```

Inside the container, build the proofs and extracted tools:

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

By default, `polopt` requests affine scheduling and rectangular tiling.
The command prints the target under `Optimized Loop`; a successful tiling
check reports `[tiling-validation] route=permutable-band` on stderr.
Output is structured loop text. See [Environment](ENVIRONMENT.md) for build
requirements and [polopt](POLOPT.md) for options and examples.

## Compilation

The parser reads a `.loop` program. Verified extraction converts its loops
and instructions into a polyhedral model. Pluto proposes changes to statement
domains and schedules, which the corresponding validators check. For parallel
output, an independence check certifies the selected iterations. Verified
code generation then constructs the target loop nest.

Successful compilation guarantees semantic refinement from source loop IR to
target loop IR. The formalization is parameterized by the instruction language
and its semantics; the executable frontend uses `SInstr` for scalar and array
computations. Parsing, printing, and full C integration are outside the proof
boundary. The [pipeline guide](doc/VERIFIED_PIPELINE.md) explains the stages
and semantic scope.

The `polopt` executable runs the loop-to-loop compiler.
[`polcert`](POLCERT.md) provides standalone checks for externally supplied
polyhedral models.

## Documentation

| Topic | Documents |
| --- | --- |
| Build and use | [Environment](ENVIRONMENT.md), [loop syntax](syntax/README.md), [polopt](POLOPT.md), [polcert](POLCERT.md) |
| Compiler and proofs | [Verified pipeline](doc/VERIFIED_PIPELINE.md), [proof reading guide](doc/PROOF_READING_GUIDE.md) |
| Implementation interfaces | [Driver and flags](doc/POLOPT_FLAG_GUIDE.md), [Pluto interface](doc/PLUTO_INTERFACE.md) |
| Tests and experiments | [Testing](doc/TESTING.md), [Evaluation](doc/EVALUATION.md) |

Default CI builds the proofs and tools and runs regressions. Full Evaluation
experiments are manual. Builds pin the fixed Pluto revision in
[`tools/ci/pluto-baseline.env`](tools/ci/pluto-baseline.env); a separate
`buggy` branch supplies the historical versions used by bug replays.
