# Parallel Coordinate Regressions

This suite checks `--parallel-current d`, where `d` is a zero-based canonical
padded schedule coordinate. It verifies independence and the placement of
`parallel for` in generated loops.

```sh
make test-parallel-current-suite
```

The [suite manifest](suite_manifest.json) specifies positive effects and
negative requests. Expect every check to pass, including rejection of
dependence-carrying coordinates. [Scoped-hint tests](../../tests/parallel-scope/README.md)
separately cover Pluto hints restricted to particular statements.

## Diamond Examples

```sh
./polopt --diamond-tile --parallel-current 0 \
  tools/parallel_current/fixtures/diamond-example-inner-batch.loop
./polopt --diamond-tile --parallel-current 0 \
  tools/parallel_current/fixtures/jacobi-batch.loop
```

Both fixtures add an independent batch dimension to a stencil computation.
Expect a parallel batch loop, tile-size expressions, and coupled coordinates
that reconstruct the skewed source indices. The two-statement Jacobi case
must retain both array updates.

The manifest contains the exact structural checks. Some outputs retain raw
singleton reconstruction loops because cleanup cannot establish the required
trace correspondence. Those loops are part of certified code generation;
their presence is not a validator failure.
