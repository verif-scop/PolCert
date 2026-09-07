# Best Generated Perf Pipelines

This saved report reflects the supplied runtime-search records, not a measurement of the current checkout. See [the harness guide](README.md) before reusing these choices.

Notes:

- Baseline is always the unoptimized `input.loop` compiled into the same generated whole-C harness.
- Every selected optimized result goes through `polopt`; baseline is **not** eligible as a best pipeline.
- `identity` is only a last-resort `polopt --identity` fallback when all real optimization routes are slower.
- Values are generated-executable runtimes on the recorded parameters and machine, not compiler timings.
- In these records, `iss` / `iss_parallel_4` means the `--iss` route measured best; it does **not** by itself prove that Pluto actually performed ISS statement splitting on that case.

## Pipeline Counts

- default no-ISS affine+tiling pipeline: `9`
- affine-only pipeline: `9`
- ISS-enabled sequential pipeline: `10`
- parallel route (4 threads): `13`
- ISS + parallel route (4 threads): `6`
- identity-only fallback: `15`

## Per-Case Table

| Case | Selected pipeline | Flags | Speedup | Optimized time (s) | Parallel annotation |
|---|---|---|---:|---:|---|
| 1dloop-invar | default no-ISS affine+tiling pipeline | (default) | 1.075x | 0.0011 | no |
| adi | identity-only fallback | `--identity` | 0.975x | 3.1687 | no |
| advect3d | ISS-enabled sequential pipeline | `--iss` | 1.197x | 1.3326 | no |
| corcol | affine-only pipeline | `--affine-only` | 4.032x | 0.4251 | no |
| corcol3 | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 3.886x | 0.4886 | yes |
| costfunc | default no-ISS affine+tiling pipeline | (default) | 1.466x | 0.7711 | no |
| covcol | affine-only pipeline | `--affine-only` | 4.274x | 0.4121 | no |
| dct | identity-only fallback | `--identity` | 0.994x | 3.7103 | no |
| doitgen | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 3.968x | 1.9920 | yes |
| dsyr2k | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 2.443x | 2.1830 | yes |
| dsyrk | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 2.082x | 1.8748 | yes |
| fdtd-1d | identity-only fallback | `--identity` | 1.051x | 2.1839 | no |
| fdtd-2d | identity-only fallback | `--identity` | 1.021x | 3.7360 | no |
| floyd | ISS-enabled sequential pipeline | `--iss` | 1.042x | 1.8159 | no |
| fusion1 | identity-only fallback | `--identity` | 1.072x | 0.0038 | no |
| fusion10 | ISS-enabled sequential pipeline | `--iss` | 1.158x | 0.0013 | no |
| fusion2 | affine-only pipeline | `--affine-only` | 1.343x | 0.0012 | no |
| fusion3 | affine-only pipeline | `--affine-only` | 1.636x | 0.6195 | no |
| fusion4 | default no-ISS affine+tiling pipeline | (default) | 1.315x | 0.6808 | no |
| fusion5 | affine-only pipeline | `--affine-only` | 1.426x | 0.3230 | no |
| fusion6 | default no-ISS affine+tiling pipeline | (default) | 1.072x | 0.0037 | no |
| fusion7 | default no-ISS affine+tiling pipeline | (default) | 1.114x | 0.0027 | no |
| fusion8 | ISS-enabled sequential pipeline | `--iss` | 1.175x | 0.0010 | no |
| fusion9 | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 14.534x | 0.0992 | yes |
| gemver | affine-only pipeline | `--affine-only` | 1.472x | 0.9813 | no |
| intratileopt1 | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 1.856x | 0.8325 | yes |
| intratileopt2 | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 1.821x | 0.8414 | yes |
| intratileopt3 | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 1.448x | 1.7265 | yes |
| intratileopt4 | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 2.553x | 0.3978 | yes |
| jacobi-1d-imper | identity-only fallback | `--identity` | 1.041x | 1.6811 | no |
| jacobi-2d-imper | identity-only fallback | `--identity` | 1.025x | 1.8829 | no |
| lu | identity-only fallback | `--identity` | 0.990x | 2.9326 | no |
| matmul | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 3.705x | 0.3442 | yes |
| matmul-init | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 4.792x | 0.2733 | yes |
| matmul-seq | identity-only fallback | `--identity` | 1.011x | 2.5171 | no |
| matmul-seq3 | identity-only fallback | `--identity` | 0.993x | 3.7758 | no |
| multi-loop-param | ISS-enabled sequential pipeline | `--iss` | 1.302x | 0.0027 | no |
| multi-stmt-stencil-seq | identity-only fallback | `--identity` | 1.366x | 0.0057 | no |
| mvt | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 2.037x | 0.4368 | yes |
| mxv | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 1.205x | 1.5397 | yes |
| mxv-seq | identity-only fallback | `--identity` | 1.061x | 0.9456 | no |
| mxv-seq3 | identity-only fallback | `--identity` | 1.006x | 1.0323 | no |
| negparam | affine-only pipeline | `--affine-only` | 1.220x | 0.0011 | no |
| nodep | ISS-enabled sequential pipeline | `--iss` | 1.255x | 0.0010 | no |
| noloop | default no-ISS affine+tiling pipeline | (default) | 1.298x | 0.0011 | no |
| pca | default no-ISS affine+tiling pipeline | (default) | 1.799x | 0.5571 | no |
| polynomial | identity-only fallback | `--identity` | 0.995x | 3.4667 | no |
| seidel | ISS-enabled sequential pipeline | `--iss` | 1.089x | 3.4017 | no |
| seq | default no-ISS affine+tiling pipeline | (default) | 1.369x | 1.9029 | no |
| shift | affine-only pipeline | `--affine-only` | 1.075x | 0.9055 | no |
| spatial | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 1.336x | 1.7358 | yes |
| ssymm | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 14.735x | 0.3160 | yes |
| strmm | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 5.068x | 1.0648 | yes |
| strsm | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 7.814x | 0.9731 | yes |
| tce | identity-only fallback | `--identity` | 1.127x | 3.1905 | no |
| tmm | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 3.407x | 2.2072 | yes |
| tricky1 | affine-only pipeline | `--affine-only` | 1028.805x | 0.0019 | no |
| tricky2 | ISS-enabled sequential pipeline | `--iss` | 1.208x | 0.0011 | no |
| tricky3 | ISS-enabled sequential pipeline | `--iss` | 1.169x | 0.0011 | no |
| tricky4 | ISS-enabled sequential pipeline | `--iss` | 1.121x | 0.0011 | no |
| trisolv | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 5.673x | 0.2233 | yes |
| wavefront | default no-ISS affine+tiling pipeline | (default) | 1.514x | 1.7204 | no |
