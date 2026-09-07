# Statement-scoped parallel hints

A Pluto loop hint identifies a schedule coordinate and a set of statements.
Applying that coordinate globally can include unrelated sequential loops.

For each coordinate `r`, the hint lowering introduces two schedule slots:

| Statement | Sequential slot | Parallel slot |
| --- | --- | --- |
| Included in the hint | `0` | `r` |
| Outside the hint | `r` | `0` |

The driver first checks the original producer schedule, then validates the
lowered schedule and every requested parallel coordinate. Zero-slot removal
uses the OpenScop-to-PolyLang coordinate mapping. Missing mappings and invalid
statement numbers cannot certify a hint. The lowering does not change domains,
instructions, or accesses.

`ParallelValidator.v` proves the slot assignments. Semantic preservation is
checked by the existing affine validator; independence and parallel code
generation use the existing proved compiler. The lowering is an untrusted
proposal, not an additional assumption in the compiler correctness theorem.

This supports statement-scoped hints at different depths, including a variable
outer prefix. It does not encode arbitrary subregions of a statement domain.
A lowering that changes a required order is rejected. Successful certification
also does not guarantee that code generation preserves every parallel group:
domain splitting remains a separate limitation.

`make test-parallel-scope` runs extracted checks for local independence, variable
prefixes, different parallel depths, real dependences, unchanged payloads, and
partial multi-hint success. In the last negative test, one valid certificate
must not be treated as acceptance of both hints.

The ordinary parallel suite also checks strict local hints while leaving a
dependent phase sequential, with one-level and two-level tiling. Two-level
proposals use the same iterator-coordinate normalization as the tiling witness,
including when affine scheduling follows tiling. The driver normalizes both
proposals before comparing their domains and rebuilding the scoped schedule;
statement IDs and scattering output rows remain unchanged. These tests require
nontrivial parallel tile bounds for the independent phases and a sequential
point loop for the dependent phase.

The two-level identity case also checks the in-memory/exported statement body
against its parsed form. `make test-tiling-body-roundtrip` tests the bare-name
AST normalization used for this comparison and rejects changes to operands,
operators, constants, calls, conditionals, and read/write locations. This is
a serialization consistency check, not a substitute for semantic validation.

The separate `pluto-fixed-manifest.json` exercises
point and tile hints at three different depths. It requires the evaluation
Pluto build, including the wavefront fix: the original producer can emit an
illegal schedule for these inputs before parallel validation. Run it with
`tools/parallel_current/run_parallel_current_suite.py --polopt ./polopt
--manifest tests/parallel-scope/pluto-fixed-manifest.json` and `POLCERT_PLUTO`
set to the repaired producer. Evaluation evidence separately checks complete
parallel-group membership against that producer's C output.

`variable-prefix.loop` and `variable-prefix.expected.loop` give a source and its
intended local parallelization. They are semantic test fixtures, not an
assumption that Pluto chooses this schedule for every option combination.
