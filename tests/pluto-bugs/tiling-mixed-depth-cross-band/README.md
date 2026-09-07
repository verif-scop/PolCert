# Mixed-Depth Tiling Reverses a Dependence

The replay uses the historical compiler. The fixed fork constructs consistent
tile coordinates for the external write. Build pins and the distinction
between historical and fixed tests are documented in the
[suite overview](../README.md).

The source writes `x[1][1]` and then copies the complete array. Pluto's affine
scheduler produces the legal timestamps

```text
write:       (1, 1, 0)
copy(i, j):  (i, j, 1)
```

so the write precedes `copy(1,1)`. Rectangular tiling with tile size 2 changes
them to

```text
write:       (1, 1, 0, 0, 0)
copy(i, j):  (floor(i/2), floor(j/2), i, j, 1)
```

Now `copy(1,1)` has timestamp `(0,0,1,1,1)` and executes before the write.
The source and affine-only programs print `42`; the tiled program prints `6`.

The generated control flow is equivalent to the following wrong program:

```c
for (int I = 0; I < 2; ++I)
  for (int J = 0; J < 2; ++J) {
    if (I == 1 && J == 1)
      x[1][1] = 42;
    for (int i = 2 * I; i < 2 * I + 2; ++i)
      for (int j = 2 * J; j < 2 * J + 2; ++j)
        y[i][j] = x[i][j];
  }
```

A legal tiled form places the write at its point in tile `(0,0)`:

```c
for (int I = 0; I < 2; ++I)
  for (int J = 0; J < 2; ++J)
    for (int i = 2 * I; i < 2 * I + 2; ++i)
      for (int j = 2 * J; j < 2 * J + 2; ++j) {
        if (i == 1 && j == 1)
          x[1][1] = 42;
        y[i][j] = x[i][j];
      }
```

Pluto excludes the zero-dimensional write statement from the selected loop
band. Its band check then considers only dependences whose source and target
are both in that band, while tiling adds quotient dimensions only to the band
statements. Padding the excluded write with zero schedule rows moves it behind
the dependent copy instance.

PolCert imports the proposed source-to-tiled instance mapping and schedule as a
tiling witness. Its tiling validator detects the reversed write-to-read
dependence and returns no optimized loop.

Run the executable comparison and validator check with:

```sh
opam exec -- make test-pluto-miscompilation-tiling-mixed-depth
```

[`ISSUE_DRAFT.md`](ISSUE_DRAFT.md) contains a standalone upstream report for
this defect.
