# ISS Proposal Checks

These fixtures check index-set splitting through two interfaces: historical
Pluto debug dumps and the native `--dump-iss-bridge` export. Both reach the
extracted complete-cut checker. The complete `polopt --iss` route additionally
composes ISS refinement with extraction and subsequent compilation.

## Run

From the built repository:

```sh
make test-iss-pluto-suite
make test-iss-pluto-live-suite
```

These targets are part of base CI. Expect valid partitions to be accepted and
the mutated or incomplete proposals to be rejected. The aggregate target also
runs the [native ISS examples](../iss-native/README.md).

## Partition Requirements

Each child must retain its parent's instruction payload and have the parent
domain conjoined with its selected sides of the affine cuts. For each parent,
the checker requires every sign combination exactly once. This gives disjoint
children covering the original domain.

Positive fixtures include reverse, periodic multi-statement, Jacobi, and heat
examples. Negative controls change a halfspace, alter a payload, reuse a
statement name, or omit a required sign region.

The multi-cut fixtures isolate partition coverage:

| Fixture | Expected result |
| --- | --- |
| Complete two-cut/four-piece partition | Accept |
| `multicut_native_mismatch.bridge` | Reject: three cuts are recorded but only four regions supplied |
| `multicut_missing_piece.bridge` | Reject: one required two-cut region is missing |

## Interface and Proof Boundary

The debug-dump path uses Python to recover source payloads, domains, cuts, and
statement correspondence from Pluto's internal representation. The native
bridge supplies those fields explicitly. Neither path is an OpenScop-based
ISS importer.

The extracted checker is `checked_iss_complete_cut_shape_validate`.
[`ISSValidatorCorrect.v`](../../src/ISSValidatorCorrect.v) composes its
soundness with the semantic proof in `ISSCutSemantics.v`. Standalone acceptance
establishes the checked model's partition conditions, not correctness of an
arbitrary surrounding C program.
