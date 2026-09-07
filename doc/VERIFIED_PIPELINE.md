# Verified Pipeline

PolCert compiles a structured loop fragment into an optimized loop nest.
Pluto supplies optimization proposals; PolCert checks them and generates the
target loops. This guide describes the representations, compilation stages,
and correctness guarantee. Commands are in [polopt](../POLOPT.md), and theorem
locations are in the [proof reading guide](PROOF_READING_GUIDE.md).

## Program Representations

The [parser](../syntax/SLoopParse.ml) and [elaborator](../syntax/SLoopElab.ml)
convert `.loop` text into
[`Loop.t`](../polygen/Loop.v#L192), which contains loops,
conditionals, instruction calls, and sequences. The
[syntax guide](../syntax/README.md) describes the accepted input language.

Verified extraction converts the loop into a
[polyhedral program](../src/PolyLang.v#L80). Each
statement has an instruction, an iteration domain, a schedule, and memory-access
summaries. The domain specifies the integer iteration points at which the
instruction executes. The schedule assigns timestamps that determine execution
order, and the access summaries describe the locations read and written.
Scheduling changes these timestamps; splitting and tiling also change how
the iteration points are represented.

## Compilation Stages

The default path is:

```text
parse -> extract -> affine scheduling -> tiling -> loop generation -> print
```

Pluto proposes the affine and tiling transformations. Their verified validators
check the proposals before loop generation. The selected options can insert
index-set splitting, post-tiling scheduling, and parallelization, or omit
scheduling and tiling.

### Extraction

The [verified extractor](../src/ExtractorFrontend.v#L1432) derives statement
domains, schedules, and accesses from the source loop.
[Domain preparation](../src/StrengthenDomain.v#L100) makes enclosing bounds
available to subsequent checks. The
[extraction proof](../src/ExtractorCorrect.v#L2099) relates executions of the
source loop to executions of the resulting polyhedral program.

### Index-Set Splitting and Affine Scheduling

Index-set splitting divides a statement domain into child domains to allow
different scheduling choices in different regions. Its
[validator](../src/ISSBoolChecker.v) checks that
the children form a complete, disjoint partition and preserve the instruction
and its accesses. [`ISSValidatorCorrect.v`](../src/ISSValidatorCorrect.v#L18)
composes the checks with the partition's semantic refinement.

Affine scheduling changes execution order while retaining the instruction
instances. The [affine validator](../src/AffineValidator.v#L4422) checks that
instances whose relative order
may change can commute. Its dependence queries use the statements' domains,
accesses, and proposed schedules.

### Tiling

Tiling introduces coordinates for tiles and represents each source instance
in the tiled program. The [validator](../src/TilingBandDirectRuntime.v#L413)
checks this correspondence and the
[permutability](../src/TilingBandScheduleValidator.v#L8283) of the selected
band of schedule dimensions. For conflicting
instances with the same enclosing schedule prefix, the band condition prevents
a dependence from running backwards in any selected dimension.

The checks support rectangular, diamond, and two-level layouts and account
for statements outside the tiled loop. The tiling stage rejects proposals
that fail its correspondence or band checks.

Intra-tile scheduling and diamond routes have a subsequent affine stage.
PolCert checks that reordering separately, using the exported tiled program
as its source. The [Pluto interface](PLUTO_INTERFACE.md) describes these
intermediate exports.

### Parallelization

Pluto's hints select iterations for concurrent execution. For a selected
schedule coordinate, the [parallel validator](../src/ParallelValidator.v#L649)
compares instances with the same
enclosing prefix and different values at that coordinate. Such instances must
commute. A successful check produces a certificate for annotated code generation.

A hint may apply to only some statements. The driver translates a scoped hint
into a schedule proposal, which undergoes affine validation before the
parallel check. The same independence check supports vector annotations,
with an additional requirement that the generated loop be innermost.

### Loop Generation

[Verified code generation](../polygen/CodeGen.v#L141) reconstructs loop bounds,
guards, and instruction calls from the polyhedral program.
[Annotated code generation](../src/ParallelCodegenCorrect.v#L995) uses parallel
certificates to determine which generated loops may execute concurrently.
Cleanup simplifies the result while
preserving its semantics and execution annotations. The printer emits the
resulting loop text.

The compiler also provides constant unrolling and checked unroll-and-jam on
generated loops. If parallelization follows unroll-and-jam, it obtains fresh
certificates from the transformed loop. Their options and restrictions are
described in the [user guide](../POLOPT.md#constant-unrolling).

## Correctness and Scope

For successful compilation, every terminating target execution has a matching
source execution from the same initial state, with final states related by
`State.eq`. The component proofs compose in
[`VerifiedParallelCompilerConfig.compile_correct`](../driver/VerifiedParallelCompilerConfig.v#L536)
to establish semantic refinement for the complete loop-to-loop pipeline.
[`ExtractedPipelineCorrect.v`](../driver/ExtractedPipelineCorrect.v#L363)
connects the concrete extracted compiler to the generic proof.

A parallel loop admits interleavings that preserve the instruction order
within each iteration. Refinement holds for all interleavings allowed by this
semantics. Vector annotations currently retain sequential formal semantics;
machine SIMD lowering requires a separate correctness argument.

The formalization takes an instruction language, its state and execution
semantics, and access information through
[`INSTR`](../polygen/InstrTy.v). The interface requires sound access summaries
and a proof that nonconflicting executions commute.
[`POLIRS`](../polygen/PolIRs.v) constructs the loop and polyhedral
representations from this interface. A new instruction language can reuse
the compiler proofs once it establishes the interface laws.

The `.loop` frontend uses [`SInstr`](../syntax/SInstr.v), with symbolic
arithmetic values and distinct named memory cells, through
[`SPolIRs`](../syntax/SPolIRs.v). The repository also provides
[`CInstr`](../src/CInstr.v), a typed assignment language using CompCert values
and operations. Its [`CState`](../src/CState.v) contains CompCert environments
and memory and requires distinct named variables to occupy distinct blocks.
[`CPolIRs`](../src/CPolIRs.v) instantiates the representations for this model;
[`CPolOpt`](../driver/CPolOpt.v) exposes its optimizer entry points.

Both models use the loop-to-loop framework. A verified translation of complete
C programs into and out of loop IR remains outside this development, as do
the text parser, printer, and auxiliary C harness. Machine-width loop arithmetic
and storage-changing transformations require further treatment.

## Acceptance and Rejection

A failed required validation stage stops compilation. Non-strict parallel
hints may instead leave a sequential result; the
[user guide](../POLOPT.md#parallel-and-vector-output) describes this behavior.

Acceptance is sound, but some legal proposals can be rejected. VPL checks
rational polyhedra, so fractional solutions can cause conservative rejection
of integer-safe transformations. Verified integer normalization removes some
of these cases. Accepted inputs are also limited by the source syntax and
recognized tiling layouts.

Code generation can split a parallel group according to statement domains.
Thus, a certified optimization may differ in its generated loop structure
from Pluto's output. [Evaluation](EVALUATION.md) describes how the experiments
compare the retained optimization effects.
