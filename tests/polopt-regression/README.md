# CLI Regression Inputs

This directory provides inputs for option-dispatch and postpass regressions,
including constant unrolling, unroll-and-jam, literal strides, and invalid
controls. It also retains benchmark-derived inputs used by those checks.

The active runner is the [Pluto compatibility suite](../../doc/POLOPT_FLAG_GUIDE.md):

```sh
make test-pluto-compat-suite
```

That runner invokes the current compiler and checks each declared acceptance,
rejection, and output effect. The independent larger default-route corpus is
[polopt-generated](../polopt-generated/README.md); run it with
`make test-polopt-loop-suite`.

For a focused case, use the compatibility runner's `--only` selector. For
example:

```sh
python3 tools/polopt_flag_suites/run_pluto_compat_suite.py \
  --only const-unrolljam-constant-loop,unrolljam-context-bound-escape-rejected
```

Both checks should pass: one requires complete constant unrolling; the other
requires rejection of an invalid jam transformation. The runner's exit status
describes whether these expectations hold, not whether both compiler calls
succeeded.

The older materialization helpers in `tools/` are not the default corpus
runner. Use the linked generated suite for maintained materialization and
whole-C tests.
