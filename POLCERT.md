# polcert

`polcert` checks externally supplied polyhedral transformations without
running loop extraction or code generation. It accepts OpenScop models and
uses the same verified affine and tiling validators as `polopt`.

## Affine scheduling

```sh
./polcert before.scop after.scop
```

The models must describe the supported common instructions, domains, and
accesses. The validator checks whether the changed schedule preserves the
required dependences. This is not a validator for arbitrary C programs.

## Tiling and subsequent scheduling

```sh
./polcert --kind tiling mid.scop posttile.scop
./polcert before.scop mid.scop posttile.scop
./polcert before.scop mid.scop posttile.scop after.scop
./polcert --second-level-tile --kind tiling mid.scop posttile.scop
```

The three-file form checks affine scheduling followed by tiling. The four-file
form also checks the final affine transformation, as used by diamond tiling
and intra-tile scheduling. Intermediate files describe actual stage results;
their names alone do not establish that they form a valid pipeline.

A successful tiling check reports `permutable-band`. Unsupported layouts and
failed band conditions are rejected; solver alarms propagate as failures.
The tiling dispatcher does not fall back to general affine validation.

The [Pluto interface](doc/PLUTO_INTERFACE.md) describes how to obtain the
corresponding `.beforescheduling.scop`, `.midtransform.scop`,
`.posttile.scop`, and `.afterscheduling.scop` files.

## Index-set splitting

```sh
./polcert --iss-bridge bridge.txt
./polcert --iss-debug-dumps before.txt after.txt
```

These modes check the imported ISS structure. For an end-to-end ISS
compilation with semantic refinement, use `polopt --iss`; a standalone bridge
check is not itself a loop-to-loop compilation theorem.

## Results and scope

Inspect the exit status as well as the validation message. A command may
reject a proposal or fail to construct a supported checking problem; neither
outcome certifies that proposal. Regression tests require the expected stage
and acceptance or rejection, not merely the presence of an output file.

Parsing and OpenScop import are engineering interfaces around the extracted
validators. The formalization is parameterized by the instruction semantics;
the executable instantiation and its limitations are described in
[Verified pipeline](doc/VERIFIED_PIPELINE.md).
