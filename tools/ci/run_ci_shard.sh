#!/usr/bin/env bash
set -euo pipefail

readonly shard="${1:---list}"

list_shards() {
  # Keep the longest shard first so the host scheduler starts it immediately.
  printf '%s\n' \
    tiling-second-rejection \
    tiling-second-manifest \
    tiling-second-routes \
    tiling-compat \
    generated \
    tiling-core \
    base
}

if [[ "$shard" == --list ]]; then
  list_shards
  exit 0
fi

cd /polcert
eval "$(opam env --switch=polcert)"
source /polcert/tools/ci/ci_resources.sh

case "$shard" in
  base)
    ci_run_timed scalar-interleaved \
      python3 /polcert/tools/tiling_routes/check_scalar_interleaved_fusion.py \
        --polcert /polcert/polcert
    ci_run_timed legacy-tests bash /polcert/tools/ci/run_legacy_tests.sh
    ci_run_timed legacy-failure-gate \
      opam exec --switch=polcert -- make test-legacy-failure-gate
    ci_run_timed extracted-zero-fallback \
      opam exec --switch=polcert -- make test-extracted-zero-fallback
    ci_run_timed executable-c-correctness \
      opam exec --switch=polcert -- make test-end-to-end-c-correctness
    ci_run_timed iss-suite opam exec --switch=polcert -- make test-iss-pluto-suite
    ci_run_timed iss-live-suite opam exec --switch=polcert -- make test-iss-pluto-live-suite
    ci_run_timed pluto-bug-oracle opam exec --switch=polcert -- make test-pluto-bugs
    ;;
  tiling-core)
    ci_run_timed integer-normalization opam exec --switch=polcert -- make test-affine-integer-fastpath
    ci_run_timed parallel-scope opam exec --switch=polcert -- make test-parallel-scope
    ci_run_timed tiling-body-roundtrip opam exec --switch=polcert -- make test-tiling-body-roundtrip
    ci_run_timed direct-routes opam exec --switch=polcert -- make test-direct-only-tiling-routes
    ci_run_timed non-second-level-routes opam exec --switch=polcert -- make test-non-second-level-tiling-routes
    ci_run_timed parallel-current opam exec --switch=polcert -- make test-parallel-current-suite
    ci_run_timed vector-current opam exec --switch=polcert -- make test-vector-current-suite
    ci_run_timed diamond-tiling opam exec --switch=polcert -- make test-diamond-tiling-suite
    ;;
  tiling-compat)
    ci_run_timed pluto-compat opam exec --switch=polcert -- make test-pluto-compat-suite
    ;;
  tiling-second-rejection)
    ci_run_timed second-level-rejection \
      opam exec --switch=polcert -- make test-second-level-tile-rejection
    ;;
  tiling-second-manifest)
    ci_run_timed second-level-manifest \
      opam exec --switch=polcert -- make test-second-level-tile-manifest
    ;;
  tiling-second-routes)
    ci_run_timed second-level-routes \
      opam exec --switch=polcert -- make test-second-level-tile-routes
    ;;
  generated)
    ci_run_timed strict-generated opam exec --switch=polcert -- make test-polopt-loop-suite
    # Reuse the just-materialized 62 cases; invoking the phony Make target here
    # would rerun every Pluto transformation before the executable check.
    ci_run_timed generated-c-correctness \
      python3 /polcert/tools/end_to_end_c/run_generated_suite.py \
        --cases-root /polcert/tests/polopt-generated/cases \
        --output-root /tmp/polcert-end-to-end-generated \
        --tier smoke \
        --benchmark-repeats 1
    ci_run_timed generated-parallel-c-correctness \
      python3 /polcert/tools/end_to_end_c/run_generated_suite.py \
        --cases-root /polcert/tests/polopt-generated/cases \
        --polopt /polcert/polopt \
        --polopt-arg=--parallel \
        --output-root /tmp/polcert-end-to-end-generated-parallel \
        --tier smoke \
        --benchmark-repeats 3 \
        --omp-threads 4 \
        --require-parallelized \
        matmul corcol3 doitgen
    ci_run_timed generated-second-level-c-correctness \
      python3 /polcert/tools/end_to_end_c/run_generated_suite.py \
        --cases-root /polcert/tests/polopt-generated/cases \
        --polopt /polcert/polopt \
        --polopt-arg=--second-level-tile \
        --output-root /tmp/polcert-end-to-end-generated-second-level \
        --tier smoke \
        --benchmark-repeats 1 \
        --optimized-loop-needle='/ 256' \
        --optimized-loop-needle='8 *' \
        --optimized-loop-needle='32 *' \
        matmul-init
    ci_run_timed generated-intratile-c-correctness \
      python3 /polcert/tools/end_to_end_c/run_generated_suite.py \
        --cases-root /polcert/tests/polopt-generated/cases \
        --polopt /polcert/polopt \
        --polopt-arg=--intratileopt \
        --output-root /tmp/polcert-end-to-end-generated-intratile \
        --tier smoke \
        --benchmark-repeats 1 \
        --require-optimized-loop-differs-from-cached \
        matmul
    ;;
  *)
    printf 'unknown CI shard: %s\n' "$shard" >&2
    printf 'known shards:\n' >&2
    list_shards >&2
    exit 2
    ;;
esac
