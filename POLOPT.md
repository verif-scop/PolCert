# polopt

`polopt` optimizes programs in the [structured loop language](syntax/README.md).
Pluto proposes transformations; the extracted verified compiler checks the
proposals and generates the target loop. The default route performs affine
scheduling and rectangular tiling.

```sh
./polopt syntax/examples/matadd.loop
./polopt --notile tests/polopt-generated/inputs/matmul.loop
./polopt --second-level-tile tests/polopt-generated/inputs/matmul.loop
./polopt --parallel tests/polopt-generated/inputs/matmul.loop
```

## Choosing transformations

| Option | Effect |
| --- | --- |
| `--notile` | Affine scheduling without tiling |
| `--identity` | Preserve the source schedule |
| `--identity --tile` | Tile the source schedule |
| `--iss` | Validate index-set splitting before subsequent optimization |
| `--second-level-tile` | Request two-level tiling |
| `--diamond-tile` | Request diamond tiling |
| `--full-diamond-tile` | Use Pluto's full-dimensional diamond search |
| `--intratileopt` | Validate affine scheduling after tiling |
| `--parallel` | Certify Pluto's proposed parallel loops |
| `--parallel-strict` | Require certification of a proposed parallel loop |
| `--parallel --multipar` | Check multiple proposed parallel coordinates |
| `--parallel-current d` | Request a specific canonical schedule coordinate |
| `--vector` | Certify an innermost vector annotation |
| `--const-unroll` | Apply verified constant-bound unrolling |
| `--unrolljam` | Attempt checked loop unroll-and-jam |

The [flag guide](doc/POLOPT_FLAG_GUIDE.md) explains combinations and dispatch.
Unsupported combinations produce a diagnostic. Accepting a flag combination
does not guarantee that every proposal from Pluto can be certified.

Ordinary tiling uses a direct permutable-band validator. It checks the instance
mapping and dependence conditions for the recognized tiling layout. There is
no fallback from this check to a general affine-schedule validator. Diamond
and intra-tile scheduling routes check the subsequent affine transformation
separately.

Parallel hints identify a schedule coordinate and participating statements.
The driver may lower a local hint to a new schedule proposal, which must pass
affine validation before parallel certification. See the
[Pluto interface](doc/PLUTO_INTERFACE.md). In non-strict mode, an uncertifiable
hint can leave the corresponding loop sequential. Code generation may also
split a parallel group into separate loops.

## Controlling Pluto

Use `--pluto-compat` for the supported Pluto-style option subset:

```sh
./polopt --pluto-compat --explain \
  --tile --smartfuse --nointratileopt --noprevector --nounrolljam \
  --nodiamond-tile --noparallel tests/polopt-generated/inputs/matmul.loop
```

This uses the same verified compiler, not a separate implementation. Explicit
options such as `--tile-sizes-file FILE`, `--fusion-structure FILE`, and
`--precut-file FILE` supply Pluto control files. `--rar` enables read–read
relations in Pluto's search; validation does not depend on this option.

`--explain` shows the normalized route, `--extract-only` prints the extracted
OpenScop, and `--profile-stages` reports stage timings. Use `--help` for the
complete command-line interface. For controlled timing experiments, use the
[evaluation scripts](doc/EVALUATION.md).

## Input and semantic scope

Bounds, guards, and memory indexes must be affine. The language supports
symbolic parameters, half-open loops, scalar and array assignments, and
conjunctions of affine guards. General arithmetic and pure calls can occur in
instruction expressions; they do not make non-affine bounds extractable.

The generic correctness theorem is
`VerifiedParallelCompilerConfig.compile_correct`; the concrete extracted
endpoints are in `driver/ExtractedPipelineCorrect.v`. The theorem relates loop
IR executions. The parser, printer, and Pluto are outside that theorem.
`SInstr` does not provide full C integer, aliasing, or floating-point semantics.
Vector annotations retain the formal model's sequential semantics rather than
specifying a machine SIMD backend.

For the component proofs and composition, see
[Verified pipeline](doc/VERIFIED_PIPELINE.md) and the
[Proof reading guide](doc/PROOF_READING_GUIDE.md).
