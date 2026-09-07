# Pluto Interface

PolCert imports transformation proposals from the
[fixed Pluto fork](https://github.com/verif-scop/pluto). The build pins are in
[`tools/ci/pluto-baseline.env`](../tools/ci/pluto-baseline.env). The `buggy`
branch is used only for historical regressions.

## Phase Exports

Pluto's `--dumpscop` exports the input, pre-tiling schedule, tiled model, and
final schedule as `.beforescheduling.scop`, `.midtransform.scop`,
`.posttile.scop`, and `.afterscheduling.scop`.

| Export | Consumer |
| --- | --- |
| Before scheduling | Source side of affine validation |
| Mid-transform | Target side of affine validation and source side of tiling validation |
| Post-tile | Target side of tiling validation; source side of any subsequent affine check |
| After scheduling | Final affine result for code-generation preparation |

The tiling boundary must describe
a legal intermediate program, including statements outside the tiled nest.
Diamond and intra-tile scheduling routes then validate the following affine
transformation separately.

The importer reads OpenScop relations and normalizes their representation.
Dropping constant-zero schedule slots changes coordinate numbering, so hints
must use the recorded raw-to-canonical coordinate mapping. C nesting depth is
not a schedule coordinate.

## Parallel and Vector Hints

A Pluto loop directive identifies a scattering coordinate and participating
statements. A local parallel hint need not apply to every statement at that
coordinate. For coordinate `r`, the driver can propose two slots:

| Statement | Sequential slot | Parallel slot |
| --- | --- | --- |
| In the hint | `0` | `r` |
| Outside the hint | `r` | `0` |

This is an untrusted schedule proposal, not merely parsing normalization.
The original schedule is validated first. The new proposal then passes affine
validation, and each requested parallel coordinate passes the verified
independence check. Domains, instructions, and accesses remain unchanged.
A proposal that changes a required order is rejected.

Vector hints use the same OpenScop coordinate mapping and dependence check,
with an additional innermost-loop restriction. The driver does not reconstruct
semantic schedule coordinates or statement tie breakers from generated C.
Evaluation observers may read Pluto's generated C to compare output effects;
that observation is outside compilation.

## Representation Normalization

The remaining adapters parse relations, map raw coordinates, reconcile tiled
iterator representations, and normalize equivalent serialized instruction
bodies. Their structural checks reject mismatched payloads or missing
coordinate mappings. These checks do not replace semantic validation.

The [parallel-scope tests](../tests/parallel-scope/README.md) cover local hints,
variable prefixes, mixed-depth tiling, and instruction-body round trips.
The [tiling regressions](TESTING.md) cover the imported phase boundaries.

## Updating Pluto

Commit and test the repair in Pluto, then update `PLUTO_GIT_COMMIT` in both the
baseline file and Dockerfile defaults. Rebuild the CI image and run all shards.
Advance the historical pin only when intentionally changing the regression
baseline; it is not the previous version of every fixed compiler update.

The fixed fork's `FIXES.md` describes producer repairs; the `buggy` branch's
README describes the historical behavior. Keep these roles distinct when
changing tests. A captured historical proposal can remain a useful negative
fixture after the fixed compiler stops producing it.
