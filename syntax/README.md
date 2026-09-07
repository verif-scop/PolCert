# Loop Input Language

The `polopt` frontend reads structured loop fragments. It does not parse a
complete C translation unit. Run commands from the repository root after
[building the tools](../ENVIRONMENT.md).

## A Complete Input

```text
context(N, M);
for i in range(0, N) {
  for j in range(0, M) {
    C[i][j] = A[i][j] + B[i][j];
  }
}
```

`context` declares symbolic integer parameters. Loops use half-open bounds:
`range(0, N)` visits 0 through `N-1` and is empty when `N <= 0`.
Assignments name scalars or indexed arrays. The frontend infers the variables
used by the fragment; C declarations and allocation are not part of this syntax.

```sh
./polopt syntax/examples/matadd.loop
./polopt --extract-only syntax/examples/matadd.loop
```

The first command prints optimized loop text. The second prints an OpenScop
model containing domains, schedules, and accesses, without optimization.

## Expressions, Guards, and Strides

Bounds, guards, and array indices must be affine: constants, variables,
addition/subtraction, and multiplication by integer constants. For example,
`2*i + N - 1` is affine; `i*j` is not. Guards support `<=`, `==`, and
conjunction with `&&`.

An optional third range argument is a nonzero integer constant:

```text
for i in range(0, N, 2) {
  A[i] = 0;
}
```

Negative strides are also supported, with an exclusive lower endpoint.
Elaboration uses the stride-lowering definitions in
[`SLoopStride.v`](SLoopStride.v). Zero and symbolic strides are rejected.

Instruction right-hand sides can contain arithmetic, pure calls, conditionals,
and float literals. Their acceptance does not extend the affine control
fragment: division, arbitrary calls, disjunction, and negation are unsupported
in extracted bounds and guards. The concrete instruction model is `SInstr`;
accepting a float literal does not prove IEEE floating-point behavior.

## Reading Output

Generated loops may contain division, `min`, `max`, guards, and reconstructed
indices introduced by tiling and code generation. Parallel and vector outputs
use `parallel for` and `vector for`. The target language is richer than the
source language, so generated text may contain forms that the source extractor
cannot accept.

The CLI prints an `Optimized Loop` heading before the program. Preserve stderr
when investigating a failure: it records stage checks and producer diagnostics.
[polopt](../POLOPT.md) explains the options and expected outcomes.

## Implementation and Proof Boundary

[`SLoopParse.ml`](SLoopParse.ml) parses text;
[`SLoopElab.ml`](SLoopElab.ml) constructs source `Loop.t`.
Route selection in `SLoopRoute.ml` and dispatch in `SLoopMain.ml` invoke the
extracted compiler or its proved postpass endpoints. The target is sequential
loop IR or annotated `ParallelLoop.t`, depending on the route.

Parsing and printing are outside the compiler theorem. Cleanup of loop
expressions and singleton loops occurs in verified passes before printing.
The [pipeline guide](../doc/VERIFIED_PIPELINE.md) describes the complete compiler.

Examples are in [examples/](examples) and the
[generated input corpus](../tests/polopt-generated/inputs). The
[testing guide](../doc/TESTING.md) covers frontend and executable regressions.
