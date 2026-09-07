# Diamond tiling and phase exports

This regression checks the repaired diamond pipeline, including its
intermediate OpenScop models and final execution. Run:

```sh
opam exec -- make test-pluto-diamond-nointratile-regression
```

The fixture is a small finite-difference computation. With tile size 2, its
original C program prints `20`. An earlier phase-export change incorrectly
guarded the mandatory diamond hyperplane restoration with `--intratileopt`;
disabling that optional locality pass produced incorrect results. Restoration
must run for diamond tiling regardless of that option.

Two further conditions matter for the exported checking boundaries:

- Mixed-depth statements need consistent tile coordinates. Copying a constant
  band coordinate while dividing the corresponding varying coordinate can
  reverse a write-to-read dependence. A scalar value 1 in a size-2 tile belongs
  to tile 0, not tile 1.
- Restoring diamond coordinates must preserve the completed schedule's
  dependence constraints. With `--rar`, independent per-statement completion
  could leave dependent instances tied or reverse their order. The repaired
  producer completes the remaining constraints jointly.

The fixed producer exports the legal tiled model before subsequent affine
transformations. The regression requires direct `permutable-band` validation,
both affine phase checks, and successful code generation. It compares every
array cell against the source under three initializations, with RAR disabled
and enabled. Using a general affine validator in place of the tiling check
does not satisfy this regression.

These checks use the fixed revision from
[`tools/ci/pluto-baseline.env`](../../../tools/ci/pluto-baseline.env).
The fixes are implemented in Pluto; the importer does not append an order
recovered from generated C to repair a bad schedule.
