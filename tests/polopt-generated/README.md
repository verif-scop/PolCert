# Generated Loop Regression Corpus

This corpus checks the default `polopt` route on benchmark-derived loop inputs.
It exercises extraction, affine scheduling, direct tiling validation, code
generation, and cleanup. Run it from a built repository:

```sh
make test-polopt-loop-suite
```

The command regenerates outputs with the current compiler, then checks
[`strict_suite_manifest.json`](strict_suite_manifest.json). The manifest
requires all 62 inputs to compile, at least 50 structural changes and
50 nontrivial changes, and explicit tiled output for designated kernels.
It also names inputs that should remain unchanged.

Every loop-bearing case must report exactly one successful
`[tiling-validation] route=permutable-band`. The scalar `noloop` case must
report `status=not-applicable reason=no-loop`. A general affine check does
not satisfy the tiling requirement.

## Inputs and Generated Files

`inputs/` contains source loop fragments. The materializer writes each run to
`cases/<name>/`, with `input.loop`, `optimized.loop`, `diff.patch`,
`status.txt`, and `stderr.txt`. Materialization refreshes these files.
Some outputs are tracked snapshots; regenerate them before using them to
characterize a new compiler build.

For materialization alone:

```sh
make materialize-polopt-loop-suite
```

Input/output locations and timeouts come from
[`materialize_manifest.json`](materialize_manifest.json). The
[generated C suite](../end-to-end-generated/README.md) consumes these pairs.

## What the Measurements Mean

`changed` compares printed text. `nontrivial_changed` additionally normalizes
iterator names and removes whole-program outer guards. Neither establishes
that a particular optimization occurred.

The tiling heuristic requires added nesting and visible strip-mining bounds,
including the expected tile size. It is a regression signal for this corpus,
not a general equivalence check. For independent Pluto/PolCert effect
comparisons, use [Evaluation](../../doc/EVALUATION.md).

The default producer recipe omits RAR. Explicit-RAR configurations have
separate expectations in the CLI suite. Preserve the selected configuration
when comparing results across runs.

The formal contract is loop IR refinement; parsing, printing, and these
textual observers remain outside the theorem. See
[Verified Pipeline](../../doc/VERIFIED_PIPELINE.md).
