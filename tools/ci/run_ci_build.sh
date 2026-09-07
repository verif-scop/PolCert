#!/usr/bin/env bash
set -euo pipefail

cd /polcert
eval "$(opam env --switch=polcert)"

source /polcert/tools/ci/ci_resources.sh

# Keep the fallbacks aligned with the Docker CI target.  Large Rocq modules can
# consume several GiB each, while extracted OCaml compilation is substantially
# lighter.  Size the two phases independently so a 4-core hosted runner does
# not trade proof-build reliability for unused OCaml parallelism.
readonly max_proof_jobs="${CI_MAX_PROOF_JOBS:-2}"
readonly proof_memory_mb="${CI_PROOF_MEMORY_MB_PER_JOB:-6144}"
proof_jobs="$(ci_choose_jobs CI_PROOF_JOBS "$max_proof_jobs" "$proof_memory_mb")"
readonly proof_jobs
readonly max_build_jobs="${CI_MAX_BUILD_JOBS:-4}"
readonly build_memory_mb="${CI_BUILD_MEMORY_MB_PER_JOB:-1536}"
build_jobs="$(ci_choose_jobs CI_BUILD_JOBS "$max_build_jobs" "$build_memory_mb")"
readonly build_jobs

printf '[ci-resources] cores=%s available_memory_mb=%s proof_jobs=%s build_jobs=%s\n' \
  "$(ci_detect_cores)" "$(ci_detect_memory_mb)" "$proof_jobs" "$build_jobs"

ci_run_timed pluto-baseline \
  bash /polcert/tools/ci/check_pluto_baseline.sh
ci_run_timed route-telemetry \
  python3 /polcert/tools/tiling_routes/test_route_telemetry.py
ci_run_timed open-proof-gate-unit \
  python3 /polcert/tools/ci/test_check_open_proofs.py
ci_run_timed proof-report-unit \
  python3 /polcert/tools/regression/test_proof_report.py
ci_run_timed regression-runner-unit \
  python3 /polcert/tools/regression/test_runner_timeout.py
ci_run_timed tiling-route-summary-unit \
  python3 /polcert/tools/regression/test_tiling_route_summary.py
ci_run_timed release-provenance-unit \
  python3 /polcert/tools/regression/test_release_provenance.py
ci_run_timed unrolljam-route-unit \
  python3 /polcert/tools/regression/test_unrolljam_route_guard.py
ci_run_timed flag-manifest-unit \
  python3 /polcert/tools/polopt_flag_suites/test_manifest_runner.py
ci_run_timed strict-effect-unit \
  python3 /polcert/tests/polopt-generated/tools/test_check_polopt_cases.py
ci_run_timed generated-harness-unit \
  python3 /polcert/tools/end_to_end_c/test_generated_harness.py
ci_run_timed evaluation-inputs-unit \
  python3 /polcert/evaluation/bin/test_evaluation.py
ci_run_timed legacy-failure-gate-unit \
  bash /polcert/tools/ci/check_legacy_failure_exit.sh --self-test
ci_run_timed python-syntax \
  python3 -m py_compile \
    /polcert/tools/ci/check_open_proofs.py \
    /polcert/tools/regression/proof_report.py \
    /polcert/tools/regression/compare_rar_policy.py \
    /polcert/tools/regression/run_regression_suite.py \
    /polcert/tools/regression/test_tiling_route_summary.py \
    /polcert/tools/polopt_flag_suites/manifest_runner.py \
    /polcert/tools/polopt_flag_suites/run_pluto_compat_suite.py \
    /polcert/tests/polopt-generated/tools/check_polopt_cases.py \
    /polcert/tools/end_to_end_c/run_case.py \
    /polcert/tools/end_to_end_c/run_suite.py \
    /polcert/tools/end_to_end_c/generated_harness.py \
    /polcert/tools/end_to_end_c/run_generated_case.py \
    /polcert/tools/end_to_end_c/run_generated_suite.py \
    /polcert/tools/iss/run_iss_multicut_adversarial.py \
    /polcert/tools/iss/run_pluto_iss_suite.py \
    /polcert/tools/iss/run_pluto_iss_live_suite.py \
    /polcert/tools/pluto_bugs/pluto_versions.py \
    /polcert/tools/pluto_bugs/run_auto_affine_lp_cc_scaling.py \
    /polcert/tools/pluto_bugs/run_affine_fst_reversed.py \
    /polcert/tools/pluto_bugs/run_diamond_nointratile_reschedule.py \
    /polcert/tools/pluto_bugs/run_matmul_parallel_hint.py \
    /polcert/tools/pluto_bugs/run_notile_unrolljam_nonpermutable.py \
    /polcert/tools/pluto_bugs/run_tiling_innerpar_satvec.py \
    /polcert/tools/pluto_bugs/run_vanished_outer_parallel.py \
    /polcert/tools/diamond_tiling/run_pluto_diamond_suite.py \
    /polcert/tools/second_level_tiling/check_scheduler_flag_forwarding.py \
    /polcert/tools/second_level_tiling/check_standalone_formal_route.py \
    /polcert/tools/second_level_tiling/check_second_level_diamond_routes.py \
    /polcert/tools/second_level_tiling/check_rejected_tiling_route.py
ci_run_timed check-admitted \
  opam exec --switch=polcert -- make -s check-admitted
ci_run_timed clean make clean
ci_run_timed depend opam exec --switch=polcert -- make depend
ci_run_timed proof opam exec --switch=polcert -- make -j"$proof_jobs" proof
ci_run_timed extraction \
  opam exec --switch=polcert -- make -j"$proof_jobs" extraction
ci_run_timed proof-report \
  python3 /polcert/tools/regression/proof_report.py \
    --json-out /tmp/polcert-proof-report.json \
    --markdown-out /tmp/polcert-proof-report.md
ci_run_timed polcert-ini opam exec --switch=polcert -- make polcert.ini
ci_run_timed extraction-depend \
  opam exec --switch=polcert -- make .depend.extr
ci_run_timed polcert \
  opam exec --switch=polcert -- make -f Makefile.extr -j"$build_jobs" polcert
# Build polopt last.  The polcert link refreshes shared extracted OCaml objects;
# leaving polopt as the final target keeps every isolated test shard from
# rebuilding the same executable in its private container overlay.
ci_run_timed polopt \
  opam exec --switch=polcert -- make -f Makefile.extr -j"$build_jobs" polopt
