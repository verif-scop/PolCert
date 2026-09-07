# Standalone Validation with polcert

`polcert` checks supplied polyhedral models without running the complete
loop-to-loop compiler. It uses the affine and tiling validators also used by
`polopt`. Build instructions are in [Environment](ENVIRONMENT.md).

## Affine Scheduling

```sh
./polcert before.scop after.scop
```

Supply two OpenScop models with the supported common domains and accesses.
The checker tests whether the new schedule preserves required dependence
orders. It omits instruction bodies and relies on the supplied access
summaries and memory model. Acceptance is consequently a model-level result,
not a proof of arbitrary C-program equivalence.

## Tiling and Phase Composition

```sh
./polcert --kind tiling mid.scop posttile.scop
./polcert before.scop mid.scop posttile.scop
./polcert before.scop mid.scop posttile.scop after.scop
```

The three-file form checks affine scheduling followed by tiling. The four-file
form adds post-tiling affine validation. Add `--second-level-tile` for the
corresponding two-level layout. These files must represent actual consecutive
stage results; [Pluto interface](doc/PLUTO_INTERFACE.md) explains the exports.

A runnable positive control is:

```sh
./polcert --kind tiling \
  tools/tiling_routes/fixtures/diamond-tile-example.midtransform.scop \
  tools/tiling_routes/fixtures/diamond-tile-example.posttile.scop
```

Expect acceptance through `permutable-band`. Failed recognition, failed band
conditions, or solver alarms do not certify a proposal. Tiling has no fallback
to general affine validation.

## Index-Set Splitting

```sh
./polcert --iss-bridge bridge.txt
./polcert --iss-debug-dumps before.txt after.txt
```

These modes check imported partition structure. The
[ISS fixtures](tests/iss-pluto-dumps/README.md) describe the input formats and
positive/negative expectations. Use `polopt --iss` when the desired result is
a compiled loop with an end-to-end refinement theorem.

## Interpreting Results

Check both the exit status and diagnostic. Rejection can mean an illegal
proposal, a conservative dependence check, or unsupported input structure.
A solver alarm is a failure to certify, not evidence that the transformation
is safe. Successful standalone checks do not perform extraction or code
generation and cannot establish their guarantees.

For compiler-stage contracts and the concrete instruction model, read
[Verified Pipeline](doc/VERIFIED_PIPELINE.md).
