# `polopt` Driver and Flag Guide

This guide explains how `polopt` options select a verified compilation route.
See [POLOPT.md](../POLOPT.md) for example commands.

Four files define the driver:

- [syntax/SLoopCli.ml](../syntax/SLoopCli.ml) parses flags and reports errors.
- [syntax/SLoopRoute.ml](../syntax/SLoopRoute.ml) normalizes flags into one typed
  route.
- [syntax/SLoopDispatch.ml](../syntax/SLoopDispatch.ml) dispatches standalone
  validation actions.
- [syntax/SLoopMain.ml](../syntax/SLoopMain.ml) maps a normalized optimization
  route to an extracted verified compiler configuration.

The driver never chooses the final compiler by re-reading route-selection
booleans. It validates the complete flag set once, retains the normalized
route, configures Pluto from that route, and dispatches on the route's execution
family.

## Route Model

A normal compilation route has five independent axes.

| Axis | Choices | Default |
| --- | --- | --- |
| Schedule | affine, identity | affine |
| Structural stage | plain, ISS | plain |
| Tiling | none, one-level, two-level | one-level |
| Tile shape and order | rectangular or diamond; fixed or intra-tile optimized | rectangular with fixed intra-tile order |
| Execution | sequential, Pluto-hinted parallel, explicit-coordinate parallel, Pluto-hinted vector, explicit-coordinate vector | sequential |

Observation flags such as `--dump-input` do not create a sixth route axis.
Post-codegen transformations begin after a verified producer. `--const-unroll`
can operate directly on sequential output or on annotated parallel output; in
the latter case it unfolds only `SeqMode` loops and preserves all existing
execution annotations. Checked `--unrolljam` begins from sequential `Loop` IR
and may then be re-extracted and freshly certified for parallel output on the
currently supported affine subset.

### Schedule

The default route asks Pluto for an affine schedule. `--identity` preserves the
source schedule and skips Pluto scheduling. Because an identity schedule alone
has no tiling phase, use `--identity-tiled` (equivalent to `--identity --tile`)
when the source schedule should be tiled.

`--notile` keeps affine scheduling but stops before tiling. `--iss --notile`
uses the checked ISS transformation followed by affine scheduling and verified
code generation. Bare `--iss --identity` remains a separate unsupported route;
the checked identity-plus-ISS composition currently starts at identity tiling
or at a documented parallel/vector consumer.

### Structural Stage

`--iss` inserts index-set splitting before scheduling. ISS changes program
structure, so it selects an ISS-aware verified compiler configuration rather
than changing a printer or Pluto tuning parameter.

### Tiling

The default affine route performs one-level rectangular tiling.
`--second-level-tile` selects hierarchical two-level tiling. The level choice
is independent of the tile shape: second-level rectangular, diamond, and full
diamond routes are supported when their produced candidates validate.

There is one diamond-tiling phase with two concurrent-start search policies:

| Public option | Internal value | Pluto search constraint |
| --- | --- | --- |
| `--diamond-tile` | `Diamond OneDimensionalStart` | use one existing band dimension in the cone-complement search |
| `--full-diamond-tile` | `Diamond FullDimensionalStart` | use all eligible non-scalar band hyperplanes |

`--full-diamond-tile` therefore implies `--diamond-tile`; it is not a second
diamond pass and does not select another validator. The driver emits both Pluto
flags for the full-dimensional mode because upstream Pluto stores the base
enable bit and the full-dimensional modifier in separate option fields. Diamond
tiling cannot be combined with `--identity` or `--notile`, because it needs an
affine/skew schedule followed by tiling.

`--band-tiling-experiment` and `--legacy-generic-tiling` remain compatibility
aliases for the default, plain, one-level rectangular route. They do not select
a different validator and cannot modify ISS, identity, second-level, diamond,
parallel, or vector routes.

### Intra-Tile Optimization

`--intratileopt` lets Pluto reorder loops inside each tile. This is a supported
checked route, not a raw oracle flag. It requires a tiling phase and changes the
validated pipeline from two transformations to three:

```text
source
  -> affine or identity schedule        checked by affine validation
  -> rectangular or diamond tiling      checked by the permutable-band validator
  -> intra-tile affine rescheduling      checked by validate_general
  -> verified code generation
```

Without `--intratileopt`, the tile-only Pluto recipe passes
`--nointratileopt`, and the validated tiled program proceeds directly to code
generation. Diamond routes also use the three-stage form because their producer
has a post-tiling affine schedule.

The extracted configuration names this three-stage theorem
`RawPostTilingAffine`. The name states the actual proof composition and does not
imply diamond geometry. The OCaml driver uses the same route for diamond tiling
and rectangular intra-tile optimization.

Support is fail-closed. The driver accepts an option combination, invokes the
external Pluto producer, and compiles only if every phase validator accepts the
produced candidate. A particular input may still be rejected when Pluto emits a
candidate outside the proved recognizers.

### Parallel and Vector Execution

`--parallel` follows Pluto's loop hints and emits `parallel for` only after the
checked doall/parallel validator certifies a dimension. `--parallel-strict`
requires a certifiable hinted dimension. `--multipar` asks the same route to
certify all selected hinted coordinates.

`--parallel-current d` bypasses hint selection and asks the extracted compiler
to certify padded schedule coordinate `d`. The word `current` is retained for
command-line compatibility.

`--vector` and Pluto-compatible `--prevector` use the same dependence check as
parallelization, then impose an additional structural condition: the annotated
loop must be innermost. PolCert currently emits a checked `vector for` marker;
the formal vector semantics is sequential rather than a machine SIMD
instruction semantics. `--vector-current d` selects an explicit coordinate.

Parallel and vector selection occurs after scheduling and tiling validation.
It therefore composes with accepted rectangular, second-level, intratile,
diamond, and ISS producer routes.

## Common Commands

| Command | Normalized route |
| --- | --- |
| `./polopt file.loop` | affine, plain, rectangular one-level tiling, sequential |
| `./polopt --notile file.loop` | affine, plain, no tiling, sequential |
| `./polopt --identity file.loop` | identity, plain, no tiling, sequential |
| `./polopt --identity-tiled file.loop` | identity, plain, rectangular one-level tiling, sequential |
| `./polopt --iss file.loop` | ISS, affine, rectangular one-level tiling, sequential |
| `./polopt --iss --notile file.loop` | ISS, affine, no tiling, sequential |
| `./polopt --second-level-tile file.loop` | affine, plain, rectangular two-level tiling, sequential |
| `./polopt --diamond-tile file.loop` | affine, plain, diamond one-level tiling, sequential |
| `./polopt --full-diamond-tile --iss file.loop` | ISS, affine, full-diamond one-level tiling, sequential |
| `./polopt --intratileopt file.loop` | affine, plain, rectangular tiling plus checked intra-tile rescheduling |
| `./polopt --identity-tiled --intratileopt file.loop` | identity tiling plus checked intra-tile rescheduling |
| `./polopt --second-level-tile --intratileopt file.loop` | two-level tiling plus checked intra-tile rescheduling |
| `./polopt --parallel file.loop` | default producer followed by Pluto-hinted checked parallel execution |
| `./polopt --parallel --multipar file.loop` | default producer followed by checked multi-coordinate parallel execution |
| `./polopt --vector file.loop` | default producer followed by innermost-only checked vector execution |

These rows describe route selection. Success still depends on the validators
accepting Pluto's output for the input program.

## Rejected Combinations

Normalization rejects contradictory choices regardless of argument order:

- `--tile` with `--notile`
- `--diamond-tile` with `--nodiamond-tile`
- `--parallel` with `--noparallel`
- `--intratileopt` with `--nointratileopt`
- `--prevector` with `--noprevector`
- `--unrolljam` with `--nounrolljam`

It also rejects routes with no matching verified composition:

| Combination | Reason |
| --- | --- |
| sequential bare `--iss --identity` | ISS identity needs tiling or a checked parallel/vector consumer |
| `--identity --parallel` without `--tile` | Pluto has no tiling phase from which to obtain the requested hint |
| `--identity --vector` without `--tile` | the vector-hint route likewise needs identity tiling |
| `--second-level-tile --notile` | two-level tiling requires a tiling phase |
| `--second-level-tile --identity` without `--tile` | identity does not imply tiling |
| diamond with `--identity` or `--notile` | diamond needs affine/skew scheduling and tiling |
| `--parallel-strict` without `--parallel` | strictness refines the hinted parallel route |
| `--vector-strict` without `--vector` | strictness refines the hinted vector route |
| `--multipar` without `--parallel` | multipar refines the hinted parallel route |
| hinted and explicit parallel/vector options together | they select different execution families |
| `--intratileopt --notile` | intra-tile rescheduling requires tiles |
| `--const-unroll` with vector output | the annotated postpass is currently exposed only for parallel routes; vector combinations remain outside the CLI surface |
| `--unrolljam` with vector output | no checked composition currently rebuilds an innermost vector annotation after the postpass |
| `--unrolljam --parallel` when the result is not affine-extractable | fresh parallel certification cannot consume symbolic `Div`, `Max`, or `Min` loop controls |

Standalone validation actions cannot be mixed with optimization-route flags.
The driver also rejects more than one standalone action in one invocation.

## Pluto-Compatible Mode

Use `--pluto-compat` to pass the supported Pluto-like flag subset through the
same typed route normalizer:

```sh
./polopt --pluto-compat --explain \
  --tile --smartfuse --intratileopt --noprevector --nounrolljam \
  --rar --nodiamond-tile --noparallel \
  tests/polopt-generated/inputs/matmul.loop
```

Compatibility mode requires explicit choices for Pluto features that are on by
default in the pinned producer. For example, callers must choose
`--intratileopt` or `--nointratileopt`, `--parallel` or `--noparallel`, and a
diamond or no-diamond mode. `--explain` prints the normalized PolCert route,
oracle-only tuning flags, and compatibility notes.

Oracle tuning flags may change the candidate that Pluto proposes. They never
bypass affine, tiling, parallel, vector, or code-generation checks. See
[PLUTO_INTERFACE.md](PLUTO_INTERFACE.md) for phase exports, hint handling,
and pinned-producer updates.

## Standalone Validators

The following commands validate external artifacts instead of compiling a
`.loop` file:

```text
--validate-affine-openscop before.scop after.scop
--extract-tiling-witness-openscop before.scop after.scop
--validate-tiling-openscop before.scop after.scop
--validate-iss-debug-dumps before.txt after.txt
--validate-iss-bridge bridge.txt
--validate-iss-pluto-suite
--validate-iss-pluto-live-suite
```

`--second-level-tile` may refine tiling witness extraction or tiling
validation. Other optimization-route flags are rejected with standalone
actions.

The standalone affine action checks schedule refinement under the domains and
access summaries supplied by the two OpenScop files. Those summaries are part
of its trusted input: statement bodies are intentionally omitted by this
importer, so this command is not a C-level equivalence checker. The complete
`.loop` compiler route has a stronger boundary: it imports only Pluto's
candidate scattering and retains the source instruction, domain, and accesses.

## Observation and Profiling

`--dump-input`, `--dump-extracted-openscop`, `--dump-scheduled-openscop`, and
`--debug-scheduler` expose intermediate state without changing the normalized
route. Scheduled OpenScop dumps use the same two-stage or three-stage producer
as final compilation, including the post-tiling affine stage for intratile and
diamond routes.

`--profile-stages` measures supported sequential, non-ISS routes and then runs
the extracted compiler again as the acceptance check. It currently rejects
parallel, vector, ISS, and second-level routes. `--extract-only` stops after
OpenScop extraction. It explicitly rejects coordinate-selected parallel/vector
execution and sequential post passes; other later route choices have no effect
on the extracted OpenScop.

## Regression Coverage

`tools/polopt_flag_suites/run_pluto_compat_suite.py` checks route bindings,
rejections, output effects, and tiling-validation reports. Its intratile matrix
covers:

- plain and ISS scheduling
- one-level and two-level tiling
- affine and identity schedules
- sequential, parallel, and vector execution
- rectangular and diamond shapes
- native option parsing and order-independent contradiction rejection
- route-aligned scheduled OpenScop dumps for affine-only, identity, ISS,
  intratile, parallel, and vector execution

Run the complete suite with:

```sh
python3 tools/polopt_flag_suites/run_pluto_compat_suite.py --timeout 30
```

For a focused rerun, pass comma-separated check names through `--only`.
