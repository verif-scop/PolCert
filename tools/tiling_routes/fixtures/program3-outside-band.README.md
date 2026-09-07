# Outside-Band Dependency Regression

The source writes `X[1][1] = 42` before copying `X` to `Y`. The copy loop has no
internal dependences, but its read of `X[1][1]` depends on the preceding write.
The `.loop` file shows the source; the OpenScop files specify the proposals.

Both targets use two-level tiles with sizes 2 and 2. The added coordinates are
`I = floor(i/2)`, `II = floor(I/2)`, `J = floor(j/2)`, and `JJ = floor(J/2)`.
The copy schedule is `[1, II, JJ, I, J, i, j]`.

The safe target preserves the external write's schedule `[0, 0, 0]`. The bad
target changes only that schedule to `[1, 0, 0, 1, 1, 0, 0]`. The read at
`i = j = 1` has timestamp `[1, 0, 0, 0, 0, 1, 1]`, so it now precedes the write.
For `N >= 2` and an initial `X[1][1] != 42`, the target computes a different
`Y[1][1]`.

The pair is intentionally mixed-depth: the write has no iteration coordinates
or tile links, while the copy has two source coordinates and four added tile
coordinates. Both proposals preserve domains, bodies, and accesses. Their only
difference is the external write's schedule.

`check_complete_direct_routes.py` requires direct-band acceptance of the safe
target and rejection of the bad target. This prevents phase-local validation
from ignoring dependencies merely because one endpoint lies outside a tiled
band. A generic-checker acceptance does not satisfy the positive control.
