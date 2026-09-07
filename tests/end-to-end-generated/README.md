# generated end-to-end suite

This directory hosts the synthesized whole-C benchmark path for the generated
`polopt` regression corpus under `tests/polopt-generated/cases/*`.

Unlike the handwritten harnesses in `tests/end-to-end-c/cases/*`, this suite
does not rely on benchmark-specific wrappers. Instead it:

- reads `input.loop` and `optimized.loop`
- synthesizes complete C programs with deterministic parameter values
- declares and initializes all discovered arrays/scalars
- recompiles baseline and optimized executables
- compares their numeric summaries, with a small abs/rel tolerance for
  floating-point drift
- records end-to-end runtime for each case

This provides uniform whole-program coverage for the full generated corpus,
including fragmentary benchmarks that do not have a reusable original C driver.

The suite now supports parameter tiers through
`tests/end-to-end-generated/param_tiers.json`:

- `smoke`: conservative quick-check sizes
- `perf`: tuned toward roughly second-scale runtimes when practical
- `heavy`: one step above `perf` when a larger stable point was found

It also supports an on-the-fly optimization mode driven by `polopt`, which is
useful for benchmarking `--parallel` output without first materializing a new
`optimized.loop`. When that mode emits `parallel for`, the generated C is
compiled with OpenMP and run with the requested `OMP_NUM_THREADS`.

`--timeout-seconds` applies both to the `polopt` optimization step and to each
generated executable run, so a hung baseline or optimized binary fails the case
instead of stalling the whole suite.

The default `perf` target can also consume a per-case best-pipeline map from
`best_pipelines.json`. This lets each generated benchmark run with the fastest
validated pipeline found so far among the currently tracked candidates:

- `identity` (still runs through `polopt`, but asks for no optimization)
- `default no-ISS affine+tiling pipeline` (the current cached `optimized.loop`)
- `affine_only`
- `iss`
- `parallel_4`
- `iss_parallel_4`

Search prefers a non-`identity` pipeline whenever it yields a real positive
speedup. `identity` is only kept as a last-resort fallback.

The `parallel_4` and `iss_parallel_4` candidates are only eligible when the
generated route emits a real verified `parallel for`. A sequential fallback on
those command lines is not allowed to win the "parallel" slots.

Default CI runs the one-repeat smoke tier over all 62 materialized cases and
compares each optimized executable with its baseline. Repeated performance
runs, pipeline search, and tuning are intentionally **not** part of default CI.

The textual `.loop` to C lowering uses explicit helpers for Rocq `Z.div` and
`Z.mod` in loop bounds, guards, and array subscripts. This covers negative
intermediate values introduced by diamond schedules. Division in instruction
right-hand sides remains ordinary floating-point C division, as required by
the generated numeric kernels.

The runner rejects `NaN` and infinity even when both output strings match.
The all-pair execution check separately runs every accepted source/optimized
program configuration and requires the results to agree. General parallel
loops run repeatedly so one coincidental execution cannot hide an unstable
result.
It is a manual check, separate from the normal regression suite.

One-command refresh of the generated `perf` campaign:

```bash
opam exec -- make test-end-to-end-generated-perf-refresh
```

That target:

- refreshes the per-case best-pipeline search
- regenerates the fixed Markdown summary table
- reruns the generated `perf` tier using the chosen best pipeline per case

The resulting 62-case table lives in:

- `tests/end-to-end-generated/BEST_PIPELINES.md`

Run the generated suite at the default `perf` tier with:

```bash
opam exec -- make test-end-to-end-generated
```

Other useful entry points:

```bash
opam exec -- make test-end-to-end-generated-smoke
opam exec -- make test-end-to-end-generated-heavy
opam exec -- make test-end-to-end-generated-perf-parallel
opam exec -- make test-end-to-end-generated-slow-perf-parallel
opam exec -- make search-end-to-end-generated-best
opam exec -- make report-end-to-end-generated-best
opam exec -- make test-end-to-end-generated-perf-refresh
opam exec -- make tune-end-to-end-generated
```
