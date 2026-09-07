# Diamond tiling without intra-tile optimization

The phase-dump patch at Pluto commit `7d6fae8` accidentally guarded
`pluto_diamond_tile_reschedule` with `options->intratileopt`; the regression
remained present at audited predecessor `488ea2f`. That reschedule restores the
hyperplane temporarily evicted to construct a concurrent-start diamond
schedule. It is required for Pluto's final CLooG/AST path; it is not the
optional intra-tile locality pass controlled by `--intratileopt`.

With tile size `2` and every non-tiling optimization disabled, the original
`diamond_nointratile.c` prints `20`. The old `--diamond-tile
--nointratileopt` path printed `18`; full-diamond printed `15`. Ordinary and
two-level rectangular tiling both printed `20`. ASan and UBSan report no error,
so this is an execution-order defect rather than undefined behavior in the
fixture.

Pluto commit `56b6669` on `fix/diamond-reschedule-with-nointratileopt` makes the
restore unconditional for diamond tiling and adds the same executable
regression; this fix is not yet on `verif-scop/master`. The PolCert regression
checks both the fixed raw producer and the corresponding mixed-scalar `.loop`
candidate. Before the mixed-band fix, the no-RAR `.loop` route exported a tiled
schedule that reversed a read-after-write dependency. At `t=0, i=0, j=0`,
statement 1 writes `ey[0][0]` and statement 4 reads it. Their midpoint schedules
are `(0,1,1,2)` and `(1,1,1,3)`, respectively. The tiled schedules become
`(0,0,1,0,1,1,2)` and `(0,0,0,1,1,1,3)`, putting the read first.
The same inversion occurs at `j=2`.

Pluto treated the same band coordinate differently across statements: it
divided a varying coordinate by the tile size but copied a scalar coordinate
unchanged. With tile size 2, the scalar value 1 became tile coordinate 1 rather
than 0. The mixed-band fix gives every statement an explicit tile coordinate
whenever that band coordinate varies in any statement. Its existing domain
constraints determine the singleton tile coordinate for a scalar occurrence.

The post-tile dump remains before diamond rescheduling. This branch's regression
requires direct `permutable-band` validation, both affine phase checks, and
successful loop generation. It also compares every array cell with the original
C program under three initializations. The general-schedule route fails the test.
These checks require Pluto's `pluto-consistent-mixed-band-tiles.patch`; they do
not describe the previously published producer snapshot.

The earlier scheduling repair completed the ordinary schedule and then
reinstated diamond coordinates. With `--rar`, that exchange could reverse a
dependence that the ordinary schedule had already ordered. Joint completion
now constructs a suffix from the dependencies still unordered in either
schedule. Both RAR modes must pass direct tiling validation, both affine
checks, loop generation, and the complete-array comparisons above.

The separate typed `diamond-stencil`
positive test demonstrates that a supported pure diamond candidate is accepted
through checked tiling, post-tiling affine validation, and proved code
generation.

The ordinary artifact baseline `8c43c21` contains this earlier fix. The
historical `6f43860` checkout is retained separately for the old failing
producer and is never used by ordinary PolOpt tests.
