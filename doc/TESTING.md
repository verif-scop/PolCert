# Testing

The proof build establishes formal refinement. Executable regressions check
the surrounding implementation: extraction, CLI dispatch, serialization,
Pluto interfaces, and generated output. Retention and performance experiments
are separate manual tasks described in [Evaluation](EVALUATION.md).

## Complete Validation

From the repository root:

```sh
docker build --target ci -t polcert-ci .
bash tools/ci/run_ci_shards.sh polcert-ci
```

The image build compiles all proofs, runs the open-proof gate, extracts OCaml,
and builds `polcert` and `polopt`. Expect the proof gate to report zero open
proofs. The shard runner launches seven isolated test groups and ends with
`all 7 CI shards passed` only if each exits successfully.

The shard groups cover base regressions, generated programs, core tiling and
parallel behavior, Pluto compatibility, and three two-level tiling groups.
Per-shard logs and status files identify failed commands. A clean image build
alone does not run these executable shards.
Logs go to `${RUNNER_TEMP:-/tmp}/polcert-ci-shards/` and are replaced on the
next shard run. Set `RUNNER_TEMP` to a fresh directory to preserve a run.

## Focused Checks

Run inside the [development environment](../ENVIRONMENT.md) after building:

| Area | Command | Expected behavior |
| --- | --- | --- |
| Frontend and original examples | `make test` | Expected accept/reject cases pass |
| Quick aggregate suite | `make check-smoke` | All selected checks pass |
| Integer normalization | `make test-affine-integer-fastpath` | Integer-safe controls accepted; true conflicts rejected |
| Direct tiling | `make test-direct-only-tiling-routes` | Positive layouts use the direct band route; bad proposals rejected |
| Two-level tiling | `make test-second-level-tile-suite` | Route, layout, and rejection expectations pass |
| Diamond tiling | `make test-diamond-tiling-suite` | Required tiling and schedule effects observed |
| Parallel code generation | `make test-parallel-current-suite` | Correct coordinate annotated; dependent loops rejected |
| Scoped hints | `make test-parallel-scope` | Local hints do not certify unrelated statements |
| Serialized tiled bodies | `make test-tiling-body-roundtrip` | Equivalent forms accepted; changed instructions rejected |
| Vector annotations | `make test-vector-current-suite` | Certified innermost loops annotated |
| ISS | `make test-iss-pluto-suite test-iss-pluto-live-suite` | Complete partitions accepted; invalid partitions rejected |
| CLI combinations and postpasses | `make test-pluto-compat-suite` | Dispatch, effects, and unsupported combinations match the checks |
| Generated input corpus | `make test-polopt-loop-suite` | Materialized outputs satisfy the strict manifest |
| Executable C harnesses | `make test-end-to-end-c-correctness` | Declared effects and source/target output comparisons pass |
| Historical defects and fixed producer | `make test-pluto-bugs` | Buggy behavior reproduced and PolCert response checked; fixed regressions pass |

A regression runner's exit 0 means its expectations passed. A negative test
can therefore pass because the compiler invocation inside it failed as
expected. Read the runner's expected/actual result, not only the compiler exit.

## Executable Checks

The [C harness](../tests/end-to-end-c/README.md) executes source and target
loops with the same initialized inputs and compares their outputs. Case
metadata also specifies expected changes in the generated loop structure.
For example, the matrix-multiplication case requires tiled bounds:

```sh
python3 tools/end_to_end_c/run_case.py \
  tests/end-to-end-c/cases/matmul --polopt ./polopt \
  --output-root /tmp/polcert-c-check
```

Expect `result=ok` and `outputs_match=true` in
`/tmp/polcert-c-check/matmul/summary.json`. The harness README lists the case
families and their expected behavior. The
[generated harness](../tests/end-to-end-generated/README.md) covers the larger
loop corpus using generated C wrappers.

## Historical Optimizer Defects

The [bug fixtures](../tests/pluto-bugs/README.md) use the pinned historical
Pluto through `POLCERT_BUGGY_ROOT`. Ordinary runs and fixed-producer checks
use the fixed build. A missing or mismatched compiler is a test failure.

A bug replay combines a wrong-result observation with a stage-specific
PolCert check. Each fixture describes the fault, the reproducing command,
and the expected response. Depending on the test, PolCert must reject the
proposal or return a safe result without the requested unsafe parallelism.

## Investigating a Failure

Record the command, compiler revisions, stdout, stderr, and the failing case.
First distinguish a build/environment error, producer failure, validator
rejection, missing optimization effect, and executable mismatch. Preserve
captured proposals before retrying a suite that regenerates its output directory.

Check both compiler status and the case's required effects. Printed iterator
names can change without affecting the result; missing transformations and
incorrect outputs need separate investigation.
