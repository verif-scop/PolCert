# Verified Pipeline

This note records the current theorem-facing `polopt` pipeline. It is a compact
orientation document; detailed flag coverage lives in
[POLOPT.md](../POLOPT.md) and the [flag guide](POLOPT_FLAG_GUIDE.md).

## Current contract

The main compiler wrapper is the extracted Coq compiler:

```text
VerifiedParallelCompilerConfig.compile : raw_config -> Loop.t -> imp ParallelLoop.t
```

The main theorem is `VerifiedParallelCompilerConfig.compile_correct`.
For any accepted `raw_config`, if the compiler returns a `ParallelLoop.t` target,
every terminating target execution is matched by a source `Loop.t` execution with
`State.eq` final states. `compile_verified_correct` is the corresponding theorem
after `check_config` has accepted a verified config.

For `ParMode`, target semantics admits every interleaving that preserves each
iteration trace's internal order.  It does not assume that the chosen
interleaving is safe.  The checker certifies pairwise commutativity at a padded
schedule coordinate, the code-generation origin proof relates that coordinate
to the generated loop and its actual trace, and the correctness proof derives
the ordered proof companion needed to serialize the interleaving.  This chain
also covers nested and multi-coordinate annotations.

Sequential routes are not outside this theorem. They are lifted into
`ParallelLoop.t` with all-`SeqMode` annotations. Parallel routes return the same
target language after running the parallel checker and adding `ParMode`
annotations.  Metadata-preserving cleanup is proved by reflection to the same
certified raw program; if a proof-relevant cleanup stage is not trace-safe, the
checked route returns the standard-raw program instead.

## Executable `polopt` shape

A normal schedule, tiling, or parallel optimizer run has this shape:

```text
.loop text
-> parser / elaborator
-> Loop.t
-> Pluto-compatible flag filtering and route normalization
-> optional Pluto oracle calls for schedules, tiling phases, or annotations
-> checked route construction
-> VerifiedParallelCompilerConfig.compile
-> ParallelLoop.t
-> printer / generated-loop checks
```

Pluto is an oracle: it proposes schedules, phase outputs, and loop annotation
hints. PolOpt accepts those artifacts only through checked routes.

For a tiling boundary, the extracted dispatcher runs the direct semantic
permutable-band check. It checks source-ordered WW, WR, and RW conflicts with
the same prefix before the band for decreases in the selected band components,
using certified polyhedral emptiness queries. A successful direct check reports
`permutable-band`. If the direct checker returns `false` because the layout is
outside its recognizers or the property is not established, the candidate is
reported as `rejected`; the dispatcher does not invoke another tiling
validator. An impure solver alarm propagates instead of becoming rejection.

VPL solves rational constraints. Verified integer normalization eliminates
some fractional witnesses, but it is not a complete integer solver; remaining
spurious conflicts can conservatively reject an optimization.

This check is a semantic analogue of Pluto's fully permutable-band condition
for recognized layouts. It is not a verification of Pluto's band detector,
independent-hyperplane search, or optimization heuristics. The implementation
reuses the affine validator's certified conflict and emptiness kernels, but it
does not call the whole affine-schedule validator. Ordinary rectangular,
diamond, full-diamond, and recognized grouped/interleaved second-level layouts
can use the direct route. Source-like identity layouts and structurally
matched mixed-depth layouts use program-wide semantic schedule reconstruction;
the recognized mixed second-level shape uses a phase-aware direct bridge.
Layouts outside these proved classes are rejected. Diamond pipelines
validate their final affine leg
separately, and that leg is checked by `validate_general`.

The important route families are:

- sequential configs through `RawSeq`, including identity, affine-only, ordinary
  tiling, ISS, second-level tiling, diamond, and full-diamond compositions
  supported by the current wrapper;
- explicit one-current parallel configs such as `RawParallelCurrentDefault d`;
- Pluto-hinted one-current parallel configs selected by `--parallel`;
- Pluto-hinted multi-current parallel configs selected by `--parallel --multipar`
  and represented by the `RawParallelCurrentMany*` constructors.

Vector routes reuse the doall certificate and checked vector codegen lemmas.
Constant-bound unrolling is an independent postpass dimension of the extracted
sequential compiler rather than another copy of every producer constructor.
`compile_with_postpass_correct` composes each producer theorem with
`LoopUnroll.const_unroll_correct` and verified cleanup.

The Pluto-compatible unroll-jam route is part of the sequential endpoint.
`LoopJamValidator` retains the parameter and enclosing-iterator schedule
prefix, then checks cross-body independence within each shared outer
environment over the candidate's actual bounds.
`LoopJamBridge.checked_pair_refines_sound` converts that certificate to the
native trace premise, and `LoopJamContext` lifts each accepted pair through the
recursive lowering. The extracted theorem
`extracted_sequential_compile_with_unrolljam_correct` composes the selected
producer, optional constant unrolling, checked block/remainder unroll-jam, and
cleanup for the complete returned Loop program. The selector remains an
untrusted profitability policy, but the theorem quantifies over every selector.

## Pluto-compatible CLI

`./polopt --pluto-compat ... file.loop` accepts Pluto-style flags, rejects
unsupported combinations with explicit reasons, and dispatches the accepted
combination to the relevant checked route. The unified wrapper covers ordinary
tiling, second-level tiling, ISS combinations, diamond and full-diamond routes,
checked parallelization, and `--multipar` up to the current multi-current
certificate surface. The extracted sequential postpass endpoint covers both
constant-bound unrolling and checked unroll-jam. Constant unrolling also has an
annotated endpoint: it unfolds only `SeqMode` loops in the generated
`ParallelLoop`, so existing parallel modes and origin tags are unchanged. Its
semantic-reflection theorem composes directly with the unified parallel
compiler endpoint. For parallel unroll-jam output,
`extracted_parallel_after_unrolljam_correct` and its multi-coordinate variant
compose that endpoint with fresh identity-route extraction and parallel
validation. Constant-range block unrolling demonstrates the combination.
Symbolic block/remainder controls may contain `Div`, `Max`, or `Min`, which the
current SCoP extractor rejects; vector output also remains unsupported. This
narrow route does not claim certificate transport through arbitrary annotated
loop nests.

For `--multipar`, the driver parses Pluto's
parallel-loop hints, builds a list of candidate padded schedule coordinates, and calls a
`RawParallelCurrentMany*` config in the verified wrapper. It submits every
dimension in the finite candidate list constructed for that route. Vector routes are
innermost-only: hinted mode does not search other dimensions, and explicit
`--vector-current` rejects a non-innermost selection.

## Build and regression checks

[Testing](TESTING.md) describes the clean proof build, extraction checks, and
regression suites. [Evaluation](EVALUATION.md) provides separate manual
experiments for optimization retention and compilation overhead.

## Boundary

The current theorem family is state-preserving. The unified wrapper covers
schedule, tiling, ISS, diamond, and second-level routes that preserve the same
observable storage under `State.eq`. Parallel endpoints cover arbitrary
order-preserving interleavings justified by the checked schedule-coordinate
certificate; vector endpoints retain sequential-order vector semantics.
Unroll/jam uses its own theorem-backed component. The wrapper deliberately does not cover
storage-changing transformations such as scalar
privatization, array contraction, layout remapping, or overlapped / reuse-based
tiling. Those need a separate state relation rather than another flag in the
current wrapper.

Untrusted or non-theorem parts remain outside the Coq theorem: Pluto's search
heuristics, textual parsing and printing, OpenScop engineering, and witness
inference from external files. Those components are either treated as proposal
generators or as frontend/backend engineering around the checked core.
