# Proof Reading Guide

This guide follows the verified compiler from its semantic contract through
extraction, transformation validation, and code generation. Generate browsable
Rocq documentation with `make proof-documentation`, then open
`doc/proof-html/index.html`.

## Choosing a Compiler Theorem

Start with `VerifiedParallelCompilerConfig.compile_correct` for the
compiler with sequential, parallel, and vector output. Its concrete counterpart
is `ExtractedPipelineCorrect.extracted_parallel_compile_correct`.

The `Verified*` modules are functors over `POLIRS`; `SVerified*` modules
instantiate the executable definitions. The theorems in
`driver/ExtractedPipelineCorrect.v` connect these concrete definitions to
the generic proofs.

| Compiler | Generic correctness theorem | Concrete correctness theorem in `ExtractedPipelineCorrect` |
| --- | --- | --- |
| Sequential `Loop.t` output | `VerifiedCompilerConfig.compile_correct` | `extracted_sequential_compile_correct` |
| Annotated `ParallelLoop.t` output | `VerifiedParallelCompilerConfig.compile_correct` | `extracted_parallel_compile_correct` |

Each compiler's `compile` checks a raw configuration and then calls
`compile_verified`. The corresponding `compile_verified_correct` theorem
starts from a checked configuration; program validators still run on the
selected route. `compile_seq_verified_correct` proves the embedding of a
sequential result into `ParallelLoop.t`, and
`extracted_parallel_compile_seq_verified_correct` proves its concrete form.
Additional loop transformations have the composed endpoints listed in
[Section 8](#8-unrolling-and-jamming).

The unified dispatcher's constructors select these execution families:

| Constructor prefix | Payload | Meaning |
| --- | --- | --- |
| `VSeq` | a sequential config | Run the Loop-to-Loop dispatcher, then checked-lift the result |
| `VParallelCurrent*` | one schedule coordinate `d` | Produce one certified `ParMode` loop |
| `VVectorCurrent*` | one schedule coordinate `d` | Produce one checked innermost `VecMode` loop; its formal semantics is sequential |
| `VParallelCurrentMany*` | coordinate list `dims` | Certify and annotate every accepted coordinate |

Within the last three families, `Identity`, `IdentityTiled`, `Affine`,
`Default`, and `Diamond` choose the preprocessing route; an `ISS` suffix chooses
its ISS-aware variant. `Current` is a retained API name: `d` denotes the
canonical padded schedule coordinate used by raw code generation.

## 1. Start from the Contract

The final theorem is
`VerifiedParallelCompilerConfig.compile_correct` in
`driver/VerifiedParallelCompilerConfig.v`. Its semantic direction is:

```text
compile cfg source may return target
target executes from st to st_target
------------------------------------------------
source executes from st to some st_source
State.eq st_target st_source
```

This is the common shape of the component theorems. A validator may reject a
proposal or raise an alarm. If a checked route returns a target and that target
executes, the theorem reconstructs a source execution whose final state is
related by the abstract `State.eq` supplied by the instruction semantics.
For a `ParMode` target, the target semantics admits arbitrary interleavings that
preserve each iteration trace's internal order.  The validator certificate is
not a semantic premise.  Instead, codegen-origin theorems relate the actual
generated trace to source polyhedral instances, and the checked correctness
proof uses the certificate to construct a separate `ordered_semantics`
derivation before serializing the trace.

Read the final file in this order:

1. `VerifiedParallelCompilerConfig.compile_correct` discharges the
   raw-configuration check.
2. `VerifiedParallelCompilerConfig.compile_verified_correct` dispatches to one
   theorem per verified route.
3. `VerifiedParallelCompilerConfig.compile_seq_verified_correct` embeds a sequential loop result in the
   common parallel-loop target language.
4. `finish_strengthened_source` shows the recurring end-to-end composition:
   undo strengthening, invoke `Extractor.extractor_correct`, then compose the
   two `State.eq` facts.

The constructor cases select and compose the component theorems described below.

## 2. Semantics and Composition

The proof can be read as one chain:

```text
bounded structured loops
  -- verified extraction --> polyhedral instances
  -- checked ISS ---------> partitioned statement instances
  -- checked schedules ---> reordered fixed instances
  -- checked tiling ------> instances with tile coordinates
  -- checked annotations -> sequential, parallel, or vector loop modes
  -- verified codegen ----> structured target loops
```

Each arrow proves the same backward semantic statement. The driver composes the
arrows with transitivity of `State.eq`. A route that omits an optimization uses
an identity or shorter chain; it does not require a separate semantic model.

Two ideas recur throughout the development:

- **Representation correspondence.** The proof relates source and target
  instruction points, including their statement number, coordinates,
  instruction, access functions, and schedule.
- **Safe reordering.** If the target order reverses two source-ordered points,
  those points must commute. Bernstein-style noninterference turns absence of
  write/write, write/read, and read/write collisions into commutativity.

Affine scheduling changes only the second item. ISS and tiling also change how
statement instances are represented, so they need an additional
correspondence proof.

## 3. Extraction: Loops to Polyhedral Instances

Primary files:

- `src/ExtractorFrontend.v`: executable translation and local affine facts;
- `src/ExtractorFacts.v`: flattening, prefix slices, ordering, and partitions;
- `src/ExtractorCorrect.v`: semantic reconstruction and the public theorem;
- `src/Extractor.v`: compatibility facade only.

The extractor accepts the bounded affine fragment of the structured loop
language. It converts expressions to affine rows, accumulates loop and guard
constraints into statement domains, records affine accesses, and builds the
initial lexicographic schedule.

The proof has four layers:

1. `expr_to_aff_correct` and the test/constraint lemmas connect affine syntax
   to evaluation in a concrete iterator environment.
2. `extract_stmt` and its success-inversion lemmas expose the generated
   statements for instructions, sequences, loops, and guards.
3. The flattening and splitting lemmas in `ExtractorFacts.v` relate a sorted list of polyhedral
   instances to the syntax-directed execution of each source construct.
4. `core_sched_stmt_stmts_constrs_prefix_mutual` in `ExtractorCorrect.v` performs the structural
   induction. `extract_stmt_to_loop_semantics_core_sched_constrs` specializes
   it to the top-level empty iterator prefix, and `extractor_correct` packages
   it at the program level.

The difficult part is sequencing. Polyhedral semantics flattens all statement
instances and sorts them by timestamp, while loop semantics executes syntax
recursively. For a source sequence, the proof partitions the sorted instance
list by statement number, executes the head, rebases the tail statement
numbers, and executes the tail. For a loop, it partitions by the current
iterator value and applies the induction hypothesis to each iteration.

Recommended reading path:

```text
expr_to_aff_correct
extract_stmt_*_success_inv
extract_stmts_cons_semantics_split_by_nth_prefix_slice
core_sched_stmt_stmts_constrs_prefix_mutual
extract_stmt_to_loop_semantics_core_sched_constrs
extractor_correct
```

Most list-index and prefix lemmas support one of the two partitioning steps.
Read them on demand from the main structural proof.

## 4. ISS: One Statement to a Domain Partition

Primary files:

- `src/ISSRefinement.v`
- `src/ISSBoolChecker.v`
- `src/ISSCutSemantics.v`
- `src/ISSValidatorCorrect.v`

Index-set splitting (ISS) replaces a source statement with children whose
domains partition the source domain. The children keep the source statement's
instruction, schedule, point witness, transformations, and accesses. Only the
domain and the statement identity change.

`ISSRefinement.v` defines the declarative certificate. For each child, a
witness identifies its parent and assigns one side of every affine cut. The
central obligations establish:

- the child payload matches its parent except for the domain;
- the child domain is the parent domain conjoined with its signed cuts;
- each expected sign vector occurs exactly once for its parent;
- child domains cover the parent domain and are pairwise disjoint.

`ISSBoolChecker.v` turns those obligations into booleans and proves soundness.
`check_domain_partition_complete_cut_shapeb_sound` is the main checker theorem.

`ISSCutSemantics.v` supplies the semantic step. It maps every child instance to
the corresponding parent instance. Coverage supplies a parent for every
source point; disjointness prevents duplicate children for the same source
point; payload equality preserves instruction semantics and timestamps. The
main theorems are `iss_complete_cut_shape_to_before_poly_correct` and
`iss_complete_cut_shape_to_before_correct`.

The public composition theorem is only a few lines:

```text
checked_iss_complete_cut_shape_validate_semantics_correct
  = boolean-checker soundness
  + ISS semantic refinement
```

Read the declarative predicates before the boolean recursion. This makes the
checker appear as executable evidence for a known partition argument rather
than as the definition of ISS correctness.

## 5. Affine Scheduling: Reordering Fixed Instances

Primary file: `src/AffineValidator.v`.

The affine validator compares programs with the same statement domains and
instance coordinates but different schedules. `EqDom` records that fixed-space
correspondence. `compose_ip_ext` pairs the old and new views of an instance so
the proof can discuss both timestamps without losing its instruction and
access information.

For every ordered statement pair, `validate_two_instrs` asks whether a
source-ordered pair can be reversed by the target schedule and still have a
write/write, write/read, or read/write collision. Each question is reduced to
polyhedral emptiness. The proof then follows this chain:

```text
successful emptiness checks
  -> no conflicting access for each reversed pair
  -> the pair is Permutable_ext
  -> sorting by the new schedule preserves list semantics
  -> validate_correct / validate_tiling_correct
```

The main reading checkpoints are:

```text
validate_two_accesses_helper_correct
validate_two_instrs_implies_no_write_collision
validate_pinstrs_ext_implies_permutability
validate_implies_permutability
permutable_instance_lists_preserve_semantics
validate_correct
```

The later `*_integer` definitions repeat the guarded collision kernel with
integer-feasibility checks. They are not a second semantic argument.

The direct tiling validator imports this collision kernel, especially
`validate_two_instrs_under_guards`. It does not call the whole affine schedule
validator to justify a tiled schedule.

## 6. Tiling: Representation and Reordering

Tiling is split between a general semantic relation and executable direct
validators.

### 6.1 General tiling semantics

Primary file: `src/TilingRelation.v`.

A tiling witness says how added tile coordinates relate to the original point
coordinates. Because the target has a different point space, schedule
permutability alone is insufficient. The proof introduces an intermediate
program, `retiled_old`:

```text
after
  -- reorder in the tiled point space --> retiled_old
  -- erase the tile representation ----> before
```

The first step keeps the target's represented instances but orders them by the
lifted source schedule. `tiling_after_to_retiled_old_poly_correct` needs the
reordering-safety premise: every target reversal is a permutable pair.

The second step proves that tiled coordinates represent source points exactly
once and preserve instruction execution. The key source-based theorem is
`tiling_retiled_old_to_before_instance_correct_source`.

`tiling_after_to_before_poly_correct_via_retiled_old` composes the two
polyhedral steps.  `TilingValidator.tiling_validate_correct` lifts the argument
to complete instance-list semantics and supplies the checked representation
facts.  The relation-level composition is deliberately independent of how a
validator proves the reordering-safety premise.

Recommended reading path:

```text
tiling_rel_pinstr_structure_source
retiled_old_pinstr
before_of_retiled_old_point_source
tiling_rel_pinstr_structure_source_before_of_retiled_old_point_injective
flatten_instrs_after_implies_tiling_ext_exists
tiling_after_to_retiled_old_poly_correct
tiling_retiled_old_to_before_instance_correct_source
tiling_after_to_before_poly_correct_via_retiled_old
TilingValidator.tiling_validate_correct
```

### 6.2 Direct permutable-band validation

Primary files:

- `src/TilingBandScheduleValidator.v`
- `src/TilingBandMixedSecondValidator.v`
- `src/TilingBandPhaseScalarValidator.v`
- `src/TilingBandDirectRuntime.v`

The direct validator proves the reordering-safety premise through a semantic
permutable-band property. For each selected band component and each ordered
statement pair, it searches for a bad pair satisfying all of these conditions:

```text
the source schedule orders tau1 before tau2
the timestamps agree before the selected band
the selected band component decreases from tau1 to tau2
the pair has a WW, WR, or RW conflict
```

Certified emptiness of every bad-pair region implies that any such decreasing
pair commutes. The core semantic predicate is
`pinstr_list_semantic_componentwise_permutable`.

A second proof, called a reversal bridge in the source, connects a recognized
tiled schedule layout to that property. It shows that every target reversal
must expose a decrease in one checked component. The short central composition
is `semantic_componentwise_permutable_implies_reordering_safe`:

```text
component checker soundness + layout reversal bridge
  -> pprog_tiling_reordering_safe
```

The layout proof is where the tiling variants differ:

- `CommonBandInfrastructure` and `CommonBandDirectChecker` handle ordinary
  strip mining and uniform grouped or interleaved second-level layouts.
- `ProgramWideSemanticReconstruction` handles source-like identity,
  mixed-width, and mixed-depth schedules by reconstructing global schedule
  slots and proving that omitted slots evaluate to zero.
- `ScalarAwareBands` admits fixed scalar schedule rows around loop components.
- `PhaseAwareSemanticBands` separates statements by constant phase prefixes
  and covers phase-separated ordinary and mixed second-level layouts.
- `TilingBandMixedSecondValidator.v` and
  `TilingBandPhaseScalarValidator.v` package the specialized bridges used by
  the runtime dispatcher.

For each bridge, read the proof in five stages: invert the recognized shape;
recover the two statement witnesses; express old and target timestamps; rule
out a componentwise monotone reversal; return the decreasing component needed
by the band property. The long bridge proofs are mostly list-position and
padding arithmetic supporting those five steps.

`checked_tiling_sourceb_complete_direct_band_check_correct` in
`TilingBandDirectRuntime.v` is the runtime-facing theorem. It dispatches among
the proved layout classes. A failed recognizer or failed band check rejects the
candidate; there is no affine-validation fallback for the tiling boundary.

## 7. Parallel and Vector Annotations

Primary files:

- `polygen/ParallelLoop.v`
- `src/ParallelValidator.v`
- `src/RawCodegenOrigin.v`
- `src/ParallelCodegenCore.v`: executable tagging, cleanup checks, and
  generated/source point correspondence;
- `src/ParallelCodegenCompatibility.v`: legacy global-order wrappers plus the
  support interface used by the checked proof;
- `src/ParallelCodegenCorrect.v`: certificate ownership, actual-trace
  ordering, refinement, and checked endpoints;
- `src/ParallelCodegen.v`: compatibility facade only;
- `driver/ParallelPolOptCorrect.v`

`parallel_safe_dim_pointwise pp d` states the doall property for one padded
schedule coordinate. Two instances are in the same parallel slice when they
have the same parameter environment, the same padded timestamp prefix before
`d`, and different values at `d`. The property requires every such pair to
commute. The older flatten-list property and theorem names remain compatibility
corollaries.

`check_pprog_parallel_currentb` reduces this property to an affine validation
query between two synthetic schedule views built from the actual padded
schedule rows: one orders by the prefix followed by coordinate `d`, and the other
retains only the prefix. Dropping `d` exposes pairs in different iterations
of the same enclosing loop execution, without comparing different prefixes. Its pointwise soundness theorem is
`check_pprog_parallel_currentb_pointwise_sound`;
`checked_parallelize_current_pointwise_sound` packages the certificate. The
range theorem additionally proves that `d` is one of the schedule coordinates
inserted by code generation.

`ParallelLoop.par_trace` is the target execution model. A `ParMode` loop uses
`interleave_family`, which admits every merge that preserves each iteration
trace's internal order; it does not require commutativity. Nested parallel
loops use the same raw trace relation recursively. The separate
`ordered_par_trace` and `ordered_semantics` relations are proof companions that
carry the pairwise commutativity needed to serialize one actual execution.

`RawCodegenOrigin.v` avoids putting origin metadata in the executable target.
It reflects a sequential cover of a generated trace through LoopGen,
PolyLoopSimplifier, ASTGen, schedule elimination, and PrepareCodegen. The final
event-source theorem recovers the exact source statement, domain membership,
observable instruction effect, parameter prefix, and padded schedule
coordinates for each generated instruction point.

`ParallelCodegen.v` attaches sequential, parallel, or vector modes to generated
loops. Its central mutual proof traverses the actual raw target trace. At each
`ParMode` node it finds the owning certificate, maps two sibling-family points
back to source instances, applies pointwise certificate soundness, and transports
the resulting `Permutable` fact back to generated points. This constructs
`ordered_semantics` for the same execution; erasure then serializes it and the
existing PrepareCodegen theorem finishes the source refinement. Single-coordinate
codegen is a singleton wrapper around the multi-certificate proof. The checked
endpoints are:

```text
checked_annotated_codegen_correct_general
checked_vector_annotated_codegen_correct_general
checked_annotated_codegen_many_correct_general
```

Metadata-preserving cleanup runs after annotation. It preserves `ParMode`,
`VecMode`, and origin tags, and removes only sequential singleton loops. The
checked route tests every representation required by its reflection theorem;
an accepted cleaned execution reflects to the same certified raw program. If a
stage is not trace-safe, the route returns the checked standard-raw program.

Vectorization runs the same executable doall checker and separately requires
the emitted vector annotation to be structurally innermost. `VecMode` traces
remain in sequential order, so this theorem does not model SIMD lanes or a
vector backend execution model.

`ParallelPolOptCorrect.v` composes preprocessing routes with these annotation
and codegen theorems. The typed local lemmas
`checked_annotation_after_preparation_correct` and
`extracted_result_from_prepared_correct` expose the two repeated compositions:
first relate annotation/codegen to the prepared program and the prepared
program to its input; then undo strengthening and extraction at the frontend.
The route-specific public theorems only supply the component theorem and
compose the two explicitly named `State.eq` facts.

The semantic content of the driver layer is now explicit certificate transport:
validator success yields pointwise certificate soundness and an in-range
schedule coordinate; single and multi drivers pass those facts to the codegen
endpoints before composing the route-level `State.eq` results.

## 8. Unrolling and Jamming

These passes run on generated loop IR. Constant and block unrolling are
verified transformations; jamming is a checked reordering. Start with
[`LoopUnroll.v`](../polygen/LoopUnroll.v), then read the local fusion proof
before the recursive transformation.

`const_unroll` replaces a loop with constant bounds by a sequence of body
instances, using capture-avoiding iterator substitution. Its theorem,
`const_unroll_correct`, proves equivalence of sequential loop executions.
`block_unroll_correct` proves the corresponding result for full blocks and
remainder iterations. Unlike fusion, these transformations retain the original
instruction order and need no dependence certificate.

Jamming changes two same-range loops from `body1` followed by `body2` into one
loop that executes `body1; body2` at each iteration. The relevant proof files are:

| File | Role |
| --- | --- |
| `src/LoopJamValidator.v` | Build and check cross-body independence queries within the same enclosing environment |
| `src/LoopJamBridge.v` | Translate the extracted certificate into the native loop-trace reordering premise |
| `src/LoopJamContext.v` | Lift accepted local fusions through surrounding syntax and the selected unroll plan |
| `src/LoopJamLower.v` | Executable block/remainder construction and checked fusion attempts |

`checked_loop_jam_pair_at_depth_pointwise_sound` retains parameter and
enclosing-iterator prefixes and uses the candidate's actual bounds.
`LoopJamBridge.checked_pair_refines_sound` supplies the local refinement fact;
`LoopJamContext.checked_unrolljam_loop_with_plan_refines` composes the accepted
changes across the selected plan. The policy choosing that plan remains
untrusted. A failed local fusion can return separate loops, so success is not
a claim that every selected pair was fused.

The concrete sequential compositions are
`extracted_sequential_compile_with_postpass_correct` and
`extracted_sequential_compile_with_unrolljam_correct` in
[`ExtractedPipelineCorrect.v`](../driver/ExtractedPipelineCorrect.v).

Annotated constant unrolling has a different argument: it expands only
`SeqMode` loops and preserves existing execution modes and origin metadata.
`extracted_parallel_compile_with_const_unroll_correct` connects this pass to
the unified compiler through semantic reflection.

Unroll-and-jam followed by parallelization obtains a new certificate after
re-extraction. Read `extracted_parallel_after_unrolljam_correct` and its
multi-coordinate variant, `extracted_parallel_many_after_unrolljam_correct`.
The current extractor restricts this composition to affine-extractable
postpass output; it does not transport old certificates through arbitrary jammed
loop nests. The [C harness](../tests/end-to-end-c/README.md) gives
executable checks for these distinctions.

## 9. Reading Order

For a first complete pass, read these declarations in order:

```text
Extractor.extractor_correct
ISSValidatorCorrect.checked_iss_complete_cut_shape_validate_semantics_correct
AffineValidator.validate_correct
TilingRelation.tiling_after_to_before_poly_correct_via_retiled_old
TilingBandScheduleValidator.semantic_componentwise_permutable_implies_reordering_safe
TilingBandDirectRuntime.checked_tiling_sourceb_complete_direct_band_check_correct
ParallelValidator.checked_parallelize_current_pointwise_sound
RawCodegenOrigin.complete_generate_many_event_source
ParallelCodegen.actual_multi_ordered_mutual
ParallelCodegen.checked_annotated_codegen_correct_general
ParallelPolOptCorrect.Opt_parallel_current_correct
VerifiedParallelCompilerConfig.compile_correct
```

Then descend into the component whose premise is least clear. In particular:

- Read the extractor's mutual structural proof to understand the frontend.
- Read one ordinary and one second-level reversal bridge to understand tiling.
- Read `validate_two_instrs_implies_no_write_collision` to understand the
  shared dependence kernel.
- Skim the many route-specific `Opt_*_correct` wrappers after checking one
  example; they instantiate the same composition argument.

## 10. Maintaining the Proofs

When modifying a component or its interface:

1. Keep Boolean checker soundness separate from semantic correctness.
2. Keep tiling shape recognition separate from the semantic band property.
3. Preserve the direct tiling check. It may reuse affine collision queries,
   but it must reject a failed band check rather than fall back to the general
   affine validator.
4. Prove instance correspondence as well as reordering safety when a
   transformation changes the representation of iteration points.
5. Compose component theorems through `State.eq` in route wrappers.
6. Check exported module signatures and rebuild downstream dependencies.
   Rocq dependency fingerprints can change even when theorem statements do not.
