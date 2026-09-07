# Stage Profiling Helpers

These scripts provide reproducible `polopt --profile-stages` runs for code
generation hotspots.

## `advect3d`

To isolate affine-route code generation on `advect3d`:

```bash
python3 tools/perf/run_stage_profile.py \
  --polopt ./polopt \
  --mode affine \
  tests/polopt-generated/inputs/advect3d.loop
```

Convenience Make targets:

```bash
opam exec -- make profile-advect3d-codegen
opam exec -- make profile-advect3d-codegen-identity
```

`affine` is the default because that is the current hotspot-isolating route:
it keeps the verified affine pipeline but avoids later tiling noise.
