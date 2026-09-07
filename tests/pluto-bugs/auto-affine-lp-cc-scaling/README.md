# Automatic Affine LP Component Scaling

This fixture does not provide `.fst`, `.precut`, `skipdeps.txt`, a schedule, or
any other control file. Pluto computes the affine schedule itself with its GLPK
LP scheduler. Parallelization, tiling, vectorization, unroll-jam, intra-tile
optimization, and diamond tiling are disabled.

The four statements form two dependence components whose statement identifiers
are interleaved: `{S1,S3}` and `{S2,S4}`. Pluto's connected-component pass
overwrites the component identifier of an already visited vertex. LP schedule
integerization then scales the two ends of the `S3 -> S1` dependence by
different factors and produces an illegal affine schedule.

On the historical Pluto revision, the source prints `802469374803681347`, while
Pluto's generated program prints `11412027514774867379`. PolCert's standalone
affine checker rejects the exact before/after OpenScop pair with `overall:
FAIL`.

The complete PolCert driver follows Pluto's default and does not add `--rar`.
On the corresponding `.loop` fixture, Pluto returns an illegal candidate and
the checked route rejects it without emitting optimized Loop code. Adding
`--rar` explicitly changes Pluto's dependence-distance objective; it returns a
different, legal candidate that the checked route accepts. RAR therefore
remains an explicit oracle policy rather than a hidden compiler default.

Run:

```sh
opam exec -- make test-pluto-miscompilation-auto-affine-lp
```
