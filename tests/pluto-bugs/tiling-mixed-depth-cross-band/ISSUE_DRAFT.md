# Tiling a mixed-depth band can reverse a cross-statement dependence

## Summary

Rectangular tiling can move a loop statement before a dependent
zero-dimensional statement. The affine schedule is legal, but the tiled
schedule reverses the dependence. Pluto exits successfully and emits C with a
different result.

I reproduced this on official `bondhugula/pluto` master at
`dc462163c8b4fc97d378a4d245d1a64741cb4111`.

## Reproducer

Save the following as `tiling_mixed_depth_cross_band.c`:

```c
#include <stdio.h>

#define N 4

static int x[N][N] = {
    {1, 2, 3, 4},
    {5, 6, 7, 8},
    {9, 10, 11, 12},
    {13, 14, 15, 16},
};
static int y[N][N];

int main(void) {
  int i, j;

#pragma scop
  x[1][1] = 42;
  for (i = 0; i < N; ++i)
    for (j = 0; j < N; ++j)
      y[i][j] = x[i][j];
#pragma endscop

  printf("%d\n", y[1][1]);
  return 0;
}
```

Place the following in `tile.sizes`:

```text
2 2
```

Run:

```sh
polycc tiling_mixed_depth_cross_band.c --maxfuse --notile \
  --noparallel --nointratileopt --nodiamond-tile --noprevector \
  --nounrolljam --rar -o affine.c
polycc tiling_mixed_depth_cross_band.c --maxfuse --tile \
  --noparallel --nointratileopt --nodiamond-tile --noprevector \
  --nounrolljam --rar -o tiled.c

cc -O2 tiling_mixed_depth_cross_band.c -o original
cc -O2 affine.c -o affine
cc -O2 tiled.c -o tiled
./original
./affine
./tiled
```

Expected: all three programs print `42`.

Observed:

```text
42
42
6
```

No parallelization, diamond tiling, intra-tile rescheduling, prevectorization,
or unroll-and-jam is enabled.

## Schedule reversal

Before tiling, Pluto reports:

```text
T(S1): (1, 1, 0)
T(S2): (i, j, 1)
```

This schedule orders `S1` before the only conflicting instance, `S2(1,1)`.
After tiling, the effective schedules are:

```text
T(S1):       (1, 1, 0, 0, 0)
T(S2(i,j)):  (floor(i/2), floor(j/2), i, j, 1)
```

Consequently, `S2(1,1)` has timestamp `(0,0,1,1,1)` and executes before
`S1` at `(1,1,0,0,0)`. The copy reads the old value `6`.

The same failure occurs when the legal midpoint schedule is supplied directly
and the identity-plus-tile path is used. The illegal change is therefore in
the tiling step rather than affine schedule construction.

## Source-level cause

At the checked revision:

- `lib/polyloop.c:137-163` omits a statement from `loop->stmts` when the
  corresponding hyperplane is scalar.
- `pluto_get_permutable_band` in `lib/polyloop.c:773-824` checks a dependence
  direction only when both endpoints belong to the selected band
  (`src_in_band && dest_in_band`). The `S1 -> S2(1,1)` dependence crosses the
  band boundary and is skipped.
- `pluto_tile_band` in `lib/tile.c:121-123` adds quotient coordinates only to
  `band->loop->stmts`.
- `pluto_tile_scattering_dims` in `lib/tile.c:361-370` pads the other
  statements; `pluto_sink_transformation` in `lib/transforms.c:81-98` inserts
  zero rows. Thus `S1` is padded instead of receiving the quotient coordinates
  implied by its original `(1,1)` timestamp.

These choices are individually consistent with tiling only the selected loop
statements, but together they leave the cross-band dependence unchecked and
reverse it.

## Suggested fix and regression

Tiling should preserve dependences that cross the selected band boundary. One
way to do this is to extend the quotient-coordinate construction to every
statement whose schedule intersects the band, including zero-dimensional
statements. Alternatively, reject a band when an external statement cannot be
mapped consistently. In this example, the write must be placed at tile
coordinates `(0,0)`, derived from `floor(1/2)` in both band dimensions.

An independent lexicographic legality check after tiling would prevent this
class of error from reaching code generation. A regression can use this
four-by-four input and assert that the generated program prints `42`.
