# Evaluation

The scripts in `evaluation/` compare PolCert with Pluto for optimization
retention and compilation time. They run the current checkout on versioned
inputs and configurations. Historical optimizer defects are covered by the
[regression suite](TESTING.md#historical-optimizer-defects).

Run commands from the repository root inside the
[built development environment](../ENVIRONMENT.md). Each invocation requires
a new output directory outside `evaluation/`. Full experiments are manual;
default CI checks the consistency of their inputs and tooling. Published
measurements remain in the release package.

## Optimization Retention

### Run

Start with one matrix-multiplication case:

```sh
python3 evaluation/bin/run_evaluation.py retention \
  --cohort primary-rectangular --kernel matmul \
  --output /tmp/polcert-retention-matmul
```

The runner compiles paired inputs with an independent Pluto baseline and
PolCert, captures their outputs, and compares the optimization effects.
Expect `fresh-run.json` to report
`status=collected-and-generically-observed`. Both outputs should exhibit
rectangular tiling, with `sampled-retained` in the tiling observation.
The top-level status records completion; individual comparisons have their
own result records.

### Inputs and Configurations

A test pair consists of a source kernel and an optimization configuration.
A kernel can appear under several configurations. Retention comparisons
count pairs for which Pluto actually produces the requested effect.

Inputs come from the loop corpus, Pluto tests, and supplementary polyhedral
examples. [`plan.json`](../evaluation/manifests/plan.json) groups them into
cohorts:

| Cohort | Purpose |
| --- | --- |
| `primary-affine` | Affine reordering |
| `primary-rectangular` | One-level rectangular tiling |
| `primary-two-level` | Two-level tiling |
| `primary-diamond`, `diamond-supplement` | Diamond tiling on the common corpus and supplementary inputs |
| `primary-iss`, `iss-supplement` | Domain splitting |
| `standard-parallel` | Parallel iteration groups |
| `legacy-innerpar` | Inner-parallel selection using the alternative producer policy |
| `combined` | Selected combinations of transformations |

All cohorts use the fixed Pluto build, including `legacy-innerpar`.
Repeat `--cohort` or `--kernel` to select several entries. Omit `--kernel`
to run a cohort; omit both selectors to run the complete plan.
The generated manifest records the selected commands and inputs.
`--no-observe` collects raw proposals without running effect comparisons.

### Results

Paths below are relative to the chosen output directory:

| File or directory | Contents |
| --- | --- |
| `fresh-run.json` | Selection, executable hashes, and collection status |
| `manifests/` | Inputs and configurations selected for this run |
| `raw/<cohort>/cases/<case>/result.json` | Commands, return codes, and resource outcomes |
| `source.loop` in that case | Captured source input |
| `polcert.stdout.txt`, `polcert.stderr.txt` in that case | Final loop and stage diagnostics |
| `baseline/`, `pluto/` in that case | Independent baseline output and proposals consumed by PolCert |
| `reviews/<cohort>/cases/<case>/effect-analysis.json` | Observed effects and retention classifications |
| `trace-comparison.json`, `analysis-run.json` in that review case | Sample comparisons and observer status |
| `reviews/<cohort>/parallel/` | Parallel-group membership comparisons |
| `iss-review/review.json` | Split-partition review for `iss-supplement` |

The generic observer compares instruction and access order on bounded
executions. Tiling requires matching tile grouping on samples that cross a
tile boundary. Parallel review compares group membership, and ISS review
examines the domain partition.

`sampled-retained` means the effect agrees on the completed samples.
It is a bounded experimental result. `absent` means the producer did not
exhibit the effect. `rejected` records rejection by PolCert, while
`timeout`, `unresolved*`, and `requires-*` need investigation before a
retention conclusion. Captured proposals and observer logs distinguish
compiler rejection from an incomplete comparison.

A retention difference can have several causes. For example, code generation
may split a certified parallel group. Rational feasibility checks can also
reject an integer-safe proposal despite integer normalization. Determine the
cause from the models and generated loops when reporting such a difference.

## Compilation Overhead

### Run

```sh
python3 evaluation/bin/run_evaluation.py timing \
  --kernel 1dloop-invar --kernel dct \
  --output /tmp/polcert-timing-small
```

The timing cohort uses default rectangular tiling with standard parallel
hints. The loop-free scalar input uses its applicable nonparallel route.
Omit `--kernel` to run the full timing cohort, without concurrent builds
or benchmark workloads.

Each kernel has three uninstrumented runs of each compiler. Pluto's baseline
runs through `polycc` and generates C; PolCert reads the paired loop input
and generates loop IR text. Their difference measures complete compilation
overhead, including validation, extraction, and loop generation.
Generated-kernel runtimes are separate experiments in the
[C harness](../tests/end-to-end-c/README.md#other-workflows).

### Results

Open `measurements/timing-results.json`. A completed small run should contain
the selected kernels with empty `pending` and `failed` lists.
`publishable_measurements=false` is expected for a subset; the full-cohort
check requires complete, consistent records.

`measurements/timing-cases.csv` reports times in seconds.
Wall times are medians of three runs, and `additional_wall_seconds` is
PolCert minus Pluto. The JSON contains aggregate distributions, the ratio of
summed wall times, and the largest-cost kernels. Records for individual runs
are under `measurements/wall/`.

Timeouts, changed outputs between repetitions, and malformed profiles go into
`failed`. Report absolute overhead alongside ratios and use the stage
measurements below to identify the main costs.

### Stage Timings

One separate instrumented invocation records the following stage costs in
`measurements/phases/`:

| Stage | Attribution |
| --- | --- |
| `pluto` | Calls to the external optimizer |
| `affine_pre_validation` | Standalone affine checks before tiling |
| `affine_post_validation` | Standalone affine checks after tiling |
| `tiling_validation` | Tiling checks and their internal dependence queries |
| `parallel_validation` | Independence checks and their internal affine queries |
| `extraction` | Loop extraction |
| `codegen` | Verified loop generation |
| `others` | Conversions, cleanup, printing, and remaining driver work |

Nested calls belong to their enclosing classified stage, so each cost is
counted once. Stage times come from this single invocation, separately from
the three-run wall-time medians. The profiler is built in isolation, and its
output must match the uninstrumented compiler's output.

Check `stage_calls` and `not_invoked` before interpreting a zero time.
The catch-all `affine_validation` field should have no calls; an unclassified
standalone affine check invalidates the measurement.

### VPL Profiling

For query-construction and VPL-solving detail, build the extended profiler:

```sh
python3 evaluation/bin/build_vpl_profiler.py --source-root "$PWD" \
  --assets evaluation/assets --flavor pipeline-vpl \
  --output /tmp/polcert-vpl-profiler
python3 evaluation/bin/run_evaluation.py timing --kernel 1dloop-invar \
  --profiler-build /tmp/polcert-vpl-profiler \
  --output /tmp/polcert-timing-vpl
```

The phase records then include `vpl_details`, separating query construction
from solving within the validators.

## Maintaining the Experiments

Inputs are content-addressed. Changing an input requires updating its digest,
its manifest, and the manifest digest in the plan. Check these relationships
with:

```sh
python3 evaluation/bin/test_evaluation.py
```

After changing compiler call sites, check the profiler labels and rerun a
small timing collection. The instrumentation scripts reject unmatched call
sites.
