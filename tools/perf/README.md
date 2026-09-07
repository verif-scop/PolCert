# Diagnostic Stage Profiling

`run_stage_profile.py` wraps `polopt --profile-stages` for local diagnosis.
For example, isolate affine-only processing of `advect3d`:

```sh
python3 tools/perf/run_stage_profile.py --polopt ./polopt --mode affine \
  tests/polopt-generated/inputs/advect3d.loop
```

The convenience targets are `make profile-advect3d-codegen` and
`make profile-advect3d-codegen-identity`. Expect stage timing diagnostics and
a successfully checked optimized loop. Their purpose is to locate costly
work, not to impose a machine-independent time limit.

The underlying diagnostic mode repeats compilation for acceptance checking
and supports only a subset of sequential routes. Do not treat its process wall
time as ordinary compilation time. For uninstrumented Pluto/PolCert overhead
and disjoint stage attribution, use [Evaluation](../../doc/EVALUATION.md).
