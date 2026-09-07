# Executable C Regression Harness

This harness checks the executable integration around `polopt`. Each case
supplies a source loop, compiler options, and a C wrapper. The runner compiles
the source and optimized loops into that wrapper and compares their outputs.

Both sides use the same auxiliary loop-to-C lowering. This comparison can
detect regressions, but does not verify the lowering or establish a full
C-to-C compiler theorem. The [pipeline guide](../../doc/VERIFIED_PIPELINE.md)
states the formal boundary.

## Run and Inspect

From a built tree:

```sh
make test-end-to-end-c-correctness
```

The default CI target runs the small correctness cases and targeted parallel
and vector matrix-multiplication checks. Expect each case to report `PASS`
with matched outputs and the required structural effects. Performance-oriented
`*_perf` cases are separate.

To run one case with disposable output:

```sh
python3 tools/end_to_end_c/run_case.py \
  tests/end-to-end-c/cases/matmul \
  --polopt ./polopt --output-root /tmp/polcert-c-check
```

Read `<output-root>/<case>/summary.json`, `status.txt`, and the captured
compiler/executable output. Without `--output-root`, results go under
`tests/end-to-end-c/out/`; rerunning a case refreshes its generated files.

## What the Cases Require

Each `cases/<name>/meta.json` names the source loop and compiler flags.
It can require or forbid output patterns, parallel/vector annotations, or
complete constant unrolling. `wrapper.c.in` supplies initialization and result
printing around the `/* POLCERT_KERNEL */` insertion point.

| Case family | Required behavior |
| --- | --- |
| Tiling | Visible tiled bounds and matching execution |
| ISS | Accepted compilation and matching execution; dedicated ISS suites inspect the partition |
| Literal strides | Positive/negative iteration steps preserved |
| Parallel/vector matmul | Requested annotation present and executable output matches |
| Constant unrolling | Constant loops expanded; existing parallel loops retained |
| Unroll-and-jam | Blocks and remainders preserve execution; legal fusion accepted and dependent fusion withheld |

The unrolling cases are `const_unroll`, `parallel_const_unroll`,
`unrolljam_block_variable`, and `unrolljam_dependent_guard`. Jam cases use a
diagnostic selection policy; their metadata records the flags and expected
structure.

## Executable Comparison

The runner checks output equality and reports numeric differences, rejects
non-finite results, and applies any declared tolerances. The quality of a
comparison depends on what the wrapper prints; checksum equality is not
element-wise memory equality.

Parallel and vector cases compile with OpenMP; `vector for` lowers to
`#pragma omp simd`. Parallel correctness cases request four threads, with
repeated executions where the case metadata requires them. Timeouts cover
both optimization and execution.

The auxiliary lowering uses Rocq-style integer division and remainder for
loop bounds, guards, and indices, including negative values. Instruction
right-hand-side division follows the harness's numeric C representation.
This harness remains outside the proof.

## Other Workflows

The [generated harness](../end-to-end-generated/README.md) supplies deterministic
wrappers for the larger loop corpus. Its smoke tier is a correctness check;
runtime searches and tuning are manual experiments.

`make test-end-to-end-c-perf` runs the handwritten performance cases and
reports best-baseline/best-optimized runtime ratios. These are generated-program
runtimes, not the compilation overhead measured by [Evaluation](../../doc/EVALUATION.md).
Retain the environment and raw timings when using them.

`tools/end_to_end_c/run_program_pair_suite.py` accepts an externally supplied
program-pair index through `--index`, `--pairs-root`, and `--output-root`.
It runs accepted source/target pairs with deterministic inputs and repeated
parallel executions. This optional audit is not a default CI requirement.
Use a disposable output directory: the runner replaces it.
