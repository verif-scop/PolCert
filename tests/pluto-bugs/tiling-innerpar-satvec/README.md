# Inner-Parallel Tiling Metadata Corrupts Dependence Satisfaction

Status: reproduced, minimized, validator-catches.

The two-dimensional recurrence reads both `a[i-1][j]` and `a[i][j-1]`.
The rectangular tiling transformation is legal, but neither original schedule
dimension is parallel.

With `--identity --tile --parallel --innerpar`, pinned Pluto leaves the tile
schedule unchanged in `lib/tile.c:446-456`. It nevertheless moves inner
dependence-satisfaction bits to the outer tile dimension and clears the inner
bits at `lib/tile.c:461-478`. Later parallel-loop discovery trusts those bits
and emits an unsafe OpenMP tile loop. Generated iterator names can vary.

The fixture uses tile size `2`, so the 16-by-16 recurrence contains several
tiles while all source values remain within signed 32-bit range. The original
program prints `310235039`. The runner requires at least one of five
four-thread executions of Pluto's output to differ from this reference.

PolCert accepts the legal rectangular tiling in non-strict mode. The runner
compares every array cell with the source Loop's result and checks that each
reached parallel loop executes at most one iteration. This permits safe
singleton parallel loops while keeping dependence-carrying loops sequential.
Strict mode may reject an uncertifiable hint without emitting optimized Loop,
or accept a result that passes the same singleton and complete-state checks.
Neither mode must follow a fixed branch solely because of the producer's
schedule layout.

A separate strict negative test changes only the producer's loop-hint metadata,
preserving all domain, schedule, and access relations. Before inserting the
hint, it checks an in-domain dependence from instance `(2, 1)` to `(2, 2)`:
both access `A[2][1]`, and their first differing schedule coordinate is the
hinted tile coordinate. PolCert must reject this request without emitting
optimized Loop. The direct `--identity-tiled --parallel-current 2` check must
also reject the dependence-carrying tile loop without emitting optimized Loop.

Run the executable comparison and the phase-specific checks with:

```sh
opam exec -- make test-pluto-miscompilation-tiling-innerpar
```
