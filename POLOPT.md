# Using polopt

`polopt` compiles a structured `.loop` fragment into an optimized loop nest.
Build it using [Environment](ENVIRONMENT.md), then run these commands from the
repository root. The [syntax guide](syntax/README.md) describes inputs; the
[pipeline guide](doc/VERIFIED_PIPELINE.md) explains the verified stages.

## First Run and Results

```sh
./polopt tests/polopt-generated/inputs/matmul.loop
```

The default requests affine scheduling followed by rectangular tiling.
Successful compilation exits with code 0 and prints an `Optimized Loop`
section to stdout. Stage diagnostics go to stderr. For this example, expect
tiled loops with clipped bounds and a successful `permutable-band` diagnostic.
Iterator names and exact expressions may change between compiler versions.

Compilation failure exits nonzero, with diagnostics on stderr. These report
rejected transformations, unsupported inputs, solver alarms, or producer
failures. A failed tiling check stops compilation.

## Scheduling, Splitting, and Tiling

| Options | Requested transformation |
| --- | --- |
| `--identity` | Keep the source schedule; still extract and generate loops |
| `--notile` | Affine scheduling without tiling |
| `--identity --tile` | Tile the source schedule |
| `--iss` | Split statement domains before scheduling and tiling |
| `--second-level-tile` | Two-level tiling |
| `--diamond-tile` | Diamond tiling |
| `--full-diamond-tile` | Diamond tiling with a broader concurrent-start search |
| `--intratileopt` | Affine scheduling inside tiles after tiling |

For example:

```sh
./polopt --notile tests/polopt-generated/inputs/matmul.loop
./polopt --second-level-tile tests/polopt-generated/inputs/matmul.loop
./polopt --iss tests/end-to-end-c/cases/reverse_iss/reverse_iss.loop
```

An enabled optimization need not change every input. ISS, for example, may
return an unsplit program. Use [Evaluation](doc/EVALUATION.md) to determine
whether Pluto produced an effect and PolCert retained it.

Tiling checks the source-to-tiled instance mapping and a permutable-band
condition. Unsupported layouts or failed checks reject the proposal. Diamond
and `--intratileopt` routes separately validate the affine change after tiling.

## Parallel and Vector Output

```sh
./polopt --parallel tests/polopt-generated/inputs/matmul.loop
./polopt --parallel --parallel-strict tests/polopt-generated/inputs/matmul.loop
```

`--parallel` follows Pluto's hints. The validator checks independence between
different iterations with the same enclosing schedule prefix. Accepted
coordinates produce `parallel for`; uncertifiable hints can leave a sequential
result. `--parallel-strict` requires a certifiable hinted coordinate. A certified
singleton loop is safe but does not demonstrate useful parallelism.

`--multipar` requests multiple hinted coordinates. `--parallel-current d`
instead selects a zero-based canonical padded schedule coordinate explicitly.
This is not the nesting depth in printed C. A hint can also name a subset of
statements; see [Pluto interface](doc/PLUTO_INTERFACE.md) for its checked
translation into a schedule proposal.

`--vector` and `--vector-current d` use the same independence check and require
an innermost loop. They emit `vector for`. The formal vector semantics retains
sequential execution order; machine SIMD lowering is outside the theorem.

## After Code Generation

These options transform loops after code generation.

### Constant Unrolling

```sh
./polopt --identity --const-unroll \
  tests/end-to-end-c/cases/const_unroll/const_unroll.loop
```

`--const-unroll` replaces loops whose two bounds are integer constants with
explicit body copies in iteration order. The example produces four assignments,
including `A[3]`, with no remaining loop. Symbolic
bounds remain loops. Full expansion can produce large output, so this option
is most useful for short constant ranges.

On parallel output, the pass unfolds only sequential loops and preserves the
parallel annotations:

```sh
./polopt --identity --parallel-current 0 --const-unroll \
  tests/end-to-end-c/cases/parallel_const_unroll/parallel_const_unroll.loop
```

Expect a `parallel for` containing four explicit assignments, with its inner
constant loop removed. Vector combinations are currently rejected.

### Unroll-and-Jam

Unroll-and-jam groups consecutive outer iterations and fuses their inner loops.
PolCert applies verified block unrolling, handles the remainder, and validates
the reordering introduced by fusion. If a fusion cannot be certified, its loops
remain separate.

```sh
POLCERT_UNROLLJAM_POLICY=checked-all-depths ./polopt --pluto-compat \
  --identity --notile --nointratileopt --noprevector \
  --unrolljam --ufactor=3 --nodiamond-tile --noparallel \
  tests/end-to-end-c/cases/unrolljam_block_variable/unrolljam_block_variable.loop
```

Expect blocks of three outer iterations sharing an inner loop, plus remainder
loops for bounds not divisible by three. The example uses a diagnostic policy
that tries every eligible depth. The default `pluto-profitability` policy
selects candidates using a profitability heuristic; `--ufactor` defaults to 8.
This option uses Pluto-compatible controls, so the command states the other
producer options explicitly.

For `--parallel --unrolljam`, PolCert first transforms sequential loop IR, then
re-extracts it and obtains fresh parallel certificates. This requires an
affine-extractable result: symbolic block/remainder bounds involving division,
`min`, or `max` can prevent re-extraction. Non-strict hinted mode may return the
verified sequential result. Vector output is unsupported.

The parallel composition uses hinted `--parallel`, not `--parallel-current`:
the explicit-coordinate dispatch does not run the jam postpass. See
[Postpass Dispatch](doc/POLOPT_FLAG_GUIDE.md#postpass-dispatch) for the exact
interaction between policies and combined unroll controls.

## Pluto Controls and Inspection

Native options choose explicit PolCert routes. `--pluto-compat` accepts a
supported Pluto-style subset but requires otherwise implicit Pluto defaults
to be stated. It uses the same compiler:

```sh
./polopt --pluto-compat --explain \
  --tile --smartfuse --nointratileopt --noprevector --nounrolljam \
  --nodiamond-tile --noparallel tests/polopt-generated/inputs/matmul.loop
```

`--tile-sizes-file`, `--fusion-structure`, and `--precut-file` supply producer
control files. `--rar` adds read–read relations to Pluto's search. These options
change proposals, not the correctness checks. The
[flag guide](doc/POLOPT_FLAG_GUIDE.md) lists combination restrictions.

Use `--extract-only` for source OpenScop, `--dump-scheduled-openscop` for the
selected route's final model, and `--explain` for route selection.
`--profile-stages` is a restricted diagnostic mode that also repeats compilation
for acceptance checking. Use the [Evaluation collector](doc/EVALUATION.md),
not that mode's process wall time, for compilation-overhead comparisons.
