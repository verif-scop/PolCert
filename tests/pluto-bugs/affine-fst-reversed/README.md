# Reversed Affine Statement Order

This fixture deliberately supplies an inconsistent `.fst` statement grouping.
It tests validation of a Pluto control interface; it is not evidence that
Pluto's automatic affine scheduler independently discovers the illegal order.

The source loop writes `a[i]` and then copies that value to `b[i]`. The
`reversed.fst` control file assigns the consumer statement to scalar group `0`
and the producer to group `1`. Pluto installs that order before affine
scheduling and later marks the dependence satisfied on a positive loop
coordinate, without rejecting the earlier negative scalar coordinate.

In the historical compiler implementation at
`6f43860b6c4cddeeca09189bf3073f05b78b14a5`,
the generated program runs the complete `b` loop before the `a` loop. The
original prints `100`; Pluto's output prints `0`. The ordinary fixed Pluto
baseline rejects this candidate at its final lexicographic legality
gate.

PolCert rejects the same schedule at both useful interfaces:

- `--validate-affine-openscop` reports `overall: FAIL` for Pluto's before/after
  OpenScop pair;
- the Pluto-compatible route with `--fusion-structure reversed.fst` raises an
  alarm and emits no optimized Loop.

Run the producer, executable comparison, and both checked rejections with:

```sh
opam exec -- make test-pluto-miscompilation-affine-fst
```
