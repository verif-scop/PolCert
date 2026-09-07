# Vanished Outer Parallel Loop

Status: reproduced, minimized, validator-catches.

The outer `i` loop has exactly one iteration and is independent.  The inner
`j` loop carries the recurrence `a[0][j - 1] -> a[0][j]` and must remain
sequential.

At the pinned bug-reproduction commit
`6f43860b6c4cddeeca09189bf3073f05b78b14a5`,
the affine schedule is `(0, j)`.  CLooG therefore removes the constant outer
schedule coordinate.  `tool/ast_transform.c:75-95` then searches inward for a
loop on which to place the parallel annotation.  Its band-boundary test uses
`>` where the half-open band boundary requires `>=`, so it crosses a width-one
parallel band and marks the dependent `j` loop parallel. The ordinary fixed
Pluto baseline `8c43c21` keeps the search inside the half-open band boundary.

The raw Pluto command succeeds and produces an OpenMP program:

```sh
polycc --notile --nodiamond-tile --nointratileopt --noprevector \
  --nounrolljam --parallel vanished_outer_parallel.c
```

The original program prints `10000`. The runner requires at least one of three
four-thread executions of the generated program to differ from this reference.
This is a silent miscompilation, not merely an imprecise hint or a missed
optimization.

With `--parallel --parallel-strict`, PolCert may accept a safe singleton hint
or reject an uncertifiable hint without emitting optimized Loop. For accepted
output, the runner compares every array cell with the source Loop's result
and checks that each reached parallel loop executes at most one iteration.
These checks allow the one-iteration outer coordinate to remain parallel but
prevent its annotation from transferring to the dependent inner loop. They
do not depend on generated iterator names or a fixed schedule layout.

The separate `--notile --parallel-current 1` negative test directly requests
parallelization of the dependent inner loop and requires validator rejection.

Run the complete reproducer with:

```sh
opam exec -- make test-pluto-miscompilation-vanished-outer
```
