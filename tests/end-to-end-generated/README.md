# Generated C Harnesses

This suite turns materialized source/target loop pairs from
[polopt-generated](../polopt-generated/README.md) into executable C programs.
It synthesizes declarations, deterministic parameter values, initialization,
and numeric result summaries. Both programs use the same auxiliary lowering.

## Correctness Runs

From the repository root in the built environment:

```sh
make test-polopt-loop-suite
make test-end-to-end-generated-smoke
```

The first command regenerates loop pairs with the current compiler. The
second compiles and executes them at the small `smoke` parameter tier.
Default CI runs this one-repeat tier over the materialized corpus.

Expect every case's numeric summaries to agree within the configured
tolerances. Non-finite values and compiler/executable timeouts fail the case.
Summaries are sampled executable checks, not proofs of all-input equivalence
or complete memory equality.

For parallel output, the runner enables OpenMP and uses the requested thread
count. The textual lowering implements Rocq integer division/remainder in
bounds, guards, and indices. Both sides share that lowering, so these tests
do not independently establish its correctness.

## Runtime Experiments

[`param_tiers.json`](param_tiers.json) provides `smoke`, `perf`, and
`heavy` parameter choices. The latter two are manual runtime experiments:

```sh
make test-end-to-end-generated
make test-end-to-end-generated-heavy
```

The default generated target uses the `perf` tier, not the smoke tier.
It can consume the per-case choices in [best_pipelines.json](best_pipelines.json).
That file is a saved tuning selection, not a guarantee that those choices
remain fastest after compiler, machine, or input changes.

To search and regenerate the runtime report:

```sh
make test-end-to-end-generated-perf-refresh
```

This searches candidate routes, rewrites the saved selection and report, and
runs the selected routes. It modifies experiment files; inspect the diff before
committing. Candidate flags alone do not prove effects: parallel candidates
must emit a parallel annotation, and an ISS route need not actually split a
domain.

[BEST_PIPELINES.md](BEST_PIPELINES.md) is a saved runtime-search report.
Its numbers are machine- and parameter-specific. This workflow measures
generated executable runtime. For paired Pluto/PolCert optimization effects
and compilation overhead, use [Evaluation](../../doc/EVALUATION.md).

## Limits of the Harness

Generated wrappers make fragmented benchmark inputs executable, but differ
from original benchmark drivers. They use deterministic dimensions and result
summaries rather than exhaustive state comparison. Very short runtimes and
large ratios need repeated measurement and inspection.

Performance search, larger tiers, and tuning do not run in default CI.
Regenerate loop pairs before relying on a saved output after changing the
compiler.
