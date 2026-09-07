#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def capture_version(command: list[str]) -> str:
    try:
        proc = subprocess.run(
            command,
            cwd=str(ROOT),
            text=True,
            capture_output=True,
            timeout=10,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return "unavailable"
    if proc.returncode != 0:
        return "unavailable"
    return proc.stdout.strip() or "unavailable"


def read_build_provenance() -> dict[str, object] | None:
    path = ROOT / "BUILD_PROVENANCE.json"
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return value if isinstance(value, dict) else None


def check_build_provenance(
    environment: dict[str, str], provenance: dict[str, object] | None
) -> list[str]:
    if environment["POLCERT_REQUIRE_PROVENANCE"] != "1":
        return []
    if provenance is None:
        return ["missing or invalid BUILD_PROVENANCE.json"]

    errors: list[str] = []
    required_fields = {
        "polcert_git_commit": r"[0-9a-f]{40}",
        "polcert_release_tag": r"\S+",
        "polcert_source_archive_sha256": r"[0-9a-f]{64}",
        "pluto_git_commit": r"[0-9a-f]{40}",
        "pluto_buggy_git_commit": r"[0-9a-f]{40}",
    }
    for field, pattern in required_fields.items():
        value = provenance.get(field)
        if (
            not isinstance(value, str)
            or value == "unknown"
            or re.fullmatch(pattern, value) is None
        ):
            errors.append(f"invalid provenance field: {field}")

    environment_patterns = {
        "POLCERT_GIT_COMMIT": r"[0-9a-f]{40}",
        "POLCERT_RELEASE_TAG": r"\S+",
        "POLCERT_SOURCE_ARCHIVE_SHA256": r"[0-9a-f]{64}",
        "PLUTO_GIT_COMMIT": r"[0-9a-f]{40}",
        "PLUTO_BUGGY_GIT_COMMIT": r"[0-9a-f]{40}",
        "POLCERT_IMAGE_DIGEST": r"(?:[^@\s]+@)?sha256:[0-9a-f]{64}",
    }
    for field, pattern in environment_patterns.items():
        if (
            environment[field] == "unknown"
            or re.fullmatch(pattern, environment[field]) is None
        ):
            errors.append(f"invalid release environment field: {field}")

    comparisons = (
        ("polcert_git_commit", "POLCERT_GIT_COMMIT"),
        ("polcert_release_tag", "POLCERT_RELEASE_TAG"),
        ("polcert_source_archive_sha256", "POLCERT_SOURCE_ARCHIVE_SHA256"),
        ("pluto_git_commit", "PLUTO_GIT_COMMIT"),
        ("pluto_buggy_git_commit", "PLUTO_BUGGY_GIT_COMMIT"),
    )
    for field, environment_key in comparisons:
        if provenance.get(field) != environment[environment_key]:
            errors.append(f"provenance mismatch: {field} != {environment_key}")
    return errors


def collect_environment() -> dict[str, str]:
    buggy_root = os.environ.get(
        "POLCERT_BUGGY_ROOT", "/opt/polcert/pluto-buggy"
    )
    return {
        "POLCERT_PLUTO": os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"),
        "PLUTO_TEST_DIR": os.environ.get("PLUTO_TEST_DIR", "/pluto/test"),
        "POLCERT_GIT_COMMIT": os.environ.get("POLCERT_GIT_COMMIT", "unknown"),
        "POLCERT_RELEASE_TAG": os.environ.get("POLCERT_RELEASE_TAG", "unknown"),
        "POLCERT_SOURCE_ARCHIVE_SHA256": os.environ.get(
            "POLCERT_SOURCE_ARCHIVE_SHA256", "unknown"
        ),
        "POLCERT_IMAGE_DIGEST": os.environ.get("POLCERT_IMAGE_DIGEST", "unknown"),
        "POLCERT_REQUIRE_PROVENANCE": os.environ.get(
            "POLCERT_REQUIRE_PROVENANCE", "0"
        ),
        "PLUTO_GIT_COMMIT": capture_version(
            ["git", "-C", "/pluto", "rev-parse", "HEAD"]
        ),
        "PLUTO_BUGGY_GIT_COMMIT": capture_version(
            ["git", "-C", buggy_root, "rev-parse", "HEAD"]
        ),
        "coq_version": capture_version(["coqc", "--version"]),
        "ocaml_version": capture_version(["ocamlc", "-version"]),
    }


@dataclass
class CheckResult:
    name: str
    command: list[str]
    returncode: int
    elapsed_seconds: float
    stdout_path: str
    stderr_path: str

    @property
    def ok(self) -> bool:
        return self.returncode == 0


def build_tiling_route_summary(results: list[CheckResult]) -> dict[str, object]:
    by_name = {result.name: result for result in results}

    def passed(name: str) -> bool:
        result = by_name.get(name)
        return result is not None and result.ok

    def stdout(name: str) -> str:
        result = by_name.get(name)
        if result is None:
            return ""
        try:
            return Path(result.stdout_path).read_text(encoding="utf-8")
        except OSError:
            return ""

    direct_match = re.search(
        r"\[direct-route\] PASS expected=(\d+),fallbacks:0 "
        r"actual=\1,fallbacks:0",
        stdout("direct-only-tiling-route-smoke"),
    )
    one_level_match = re.search(
        r"\[non-second-level-routes\] PASS "
        r"expected=permutable-band:84,fallbacks:0,vector-rejections:6 "
        r"actual=permutable-band:(\d+),fallbacks:(\d+),"
        r"vector-rejections:(\d+)",
        stdout("non-second-level-tiling-routes"),
    )
    strict_loop_match = re.search(
        r"tiling_validation_permutable_band=(\d+)\s+"
        r"tiling_validation_not_applicable_no_loop=(\d+)\s+"
        r"tiling_validation_fallback=(\d+)",
        stdout("strict-loop-suite"),
    )
    strict_loop_present = "strict-loop-suite" in by_name
    strict_loop_counts = (
        tuple(map(int, strict_loop_match.groups()))
        if strict_loop_match is not None
        else None
    )

    manifest_path = ROOT / "tools" / "second_level_tiling" / "suite_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    checks = manifest["checks"]
    successful = [
        check
        for check in checks
        if check.get("expect") == "success"
        and "--second-level-tile" in check.get("args", [])
    ]
    band_marker = "[tiling-validation] route=permutable-band"
    forbidden_fallback_marker = "[tiling-validation] route=general-fallback"
    second_level_counts = {
        "manifest_checks": len(checks),
        "successful": len(successful),
        "permutable_band": sum(
            band_marker in check.get("stderr_needles", []) for check in successful
        ),
        "validation_fallback": sum(
            forbidden_fallback_marker in check.get("stderr_needles", [])
            for check in successful
        ),
        "negative": sum(check.get("expect") == "failure" for check in checks),
    }

    required = (
        "direct-only-tiling-route-smoke",
        "scalar-interleaved-tiling-route",
        "non-second-level-tiling-routes",
        "second-level-suite",
        "pluto-compat-suite",
    )
    zero_fallback_coverage = (
        direct_match is not None
        and one_level_match is not None
        and tuple(map(int, one_level_match.groups())) == (84, 0, 6)
        and second_level_counts["successful"] == 53
        and second_level_counts["permutable_band"] == 53
        and second_level_counts["validation_fallback"] == 0
        and second_level_counts["negative"] == 5
        and (
            not strict_loop_present
            or strict_loop_counts == (61, 1, 0)
        )
    )
    return {
        "schema_version": 1,
        "verified": all(passed(name) for name in required) and zero_fallback_coverage,
        "zero_tiling_validation_fallbacks": zero_fallback_coverage,
        "required_runtime_checks": {
            name: "pass" if passed(name) else "missing-or-failed" for name in required
        },
        "direct_route_smoke": {
            "cases": int(direct_match.group(1)) if direct_match else None,
            "zero_fallbacks": bool(direct_match),
        },
        "non_second_level": {
            "cases": sum(map(int, one_level_match.groups())) if one_level_match else None,
            "permutable_band": int(one_level_match.group(1)) if one_level_match else None,
            "validation_fallback": int(one_level_match.group(2)) if one_level_match else None,
            "explicit_vector_rejection": int(one_level_match.group(3)) if one_level_match else None,
        },
        "second_level_manifest": second_level_counts,
        "strict_loop_corpus": {
            "run": strict_loop_present,
            "permutable_band": (
                strict_loop_counts[0] if strict_loop_counts is not None else None
            ),
            "not_applicable_no_loop": (
                strict_loop_counts[1] if strict_loop_counts is not None else None
            ),
            "validation_fallback": (
                strict_loop_counts[2] if strict_loop_counts is not None else None
            ),
            "verified": (
                strict_loop_counts == (61, 1, 0)
                if strict_loop_present
                else None
            ),
        },
        "second_level_additional_runtime_matrix": {
            "standalone_phase_aligned": "permutable-band",
            "standalone_source_like": "permutable-band",
            "standalone_trailing_zero_normalized": "permutable-band",
            "diamond_permutable_band": 16,
            "diamond_explicit_vector_rejection": 4,
            "verified": passed("second-level-suite"),
        },
    }


def run_check(name: str, command: list[str], out_dir: Path, timeout: int | None) -> CheckResult:
    out_dir.mkdir(parents=True, exist_ok=True)
    stdout_path = out_dir / f"{name}.stdout.txt"
    stderr_path = out_dir / f"{name}.stderr.txt"
    start = time.monotonic()
    try:
        proc = subprocess.run(
            command,
            cwd=str(ROOT),
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        stdout = proc.stdout
        stderr = proc.stderr
        returncode = proc.returncode
    except subprocess.TimeoutExpired as exc:
        stdout = decode_timeout_stream(exc.stdout)
        stderr = decode_timeout_stream(exc.stderr)
        stderr += f"\n[artifact-check] timeout after {timeout} seconds\n"
        returncode = 124
    elapsed = time.monotonic() - start
    stdout_path.write_text(stdout)
    stderr_path.write_text(stderr)
    return CheckResult(
        name=name,
        command=command,
        returncode=returncode,
        elapsed_seconds=elapsed,
        stdout_path=str(stdout_path),
        stderr_path=str(stderr_path),
    )


def decode_timeout_stream(value: str | bytes | None) -> str:
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value or ""


def base_checks(
    out_dir: Path,
    diamond_timeout: int,
    identity_composition_limits: tuple[int, int] | None,
) -> list[tuple[str, list[str], int | None]]:
    identity_composition_command = [
        sys.executable,
        "tools/artifact/explore_identity_compositions.py",
        "--output-root",
        str(out_dir / "identity-compositions"),
    ]
    if identity_composition_limits is not None:
        diamond_limit, iss_limit = identity_composition_limits
        identity_composition_command.extend(
            [
                "--identity-diamond-limit",
                str(diamond_limit),
                "--identity-iss-limit",
                str(iss_limit),
            ]
        )
    return [
        (
            "py-compile-artifact-tools",
            [
                sys.executable,
                "-m",
                "py_compile",
                "tools/artifact/run_artifact_check.py",
                "tools/artifact/explore_codegen_gaps.py",
                "tools/artifact/explore_flag_effects.py",
                "tools/artifact/explore_identity_compositions.py",
                "tools/artifact/explore_unrolljam_effect_corpus.py",
                "tools/artifact/test_artifact_runner_timeout.py",
                "tools/artifact/test_tiling_route_summary.py",
                "tools/artifact/test_release_provenance.py",
                "tools/artifact/test_unrolljam_route_guard.py",
                "tools/artifact/generate_capability_matrix.py",
                "tools/artifact/proof_report.py",
                "tools/end_to_end_c/loop_to_c.py",
                "tools/end_to_end_c/run_case.py",
                "tools/end_to_end_c/runner_common.py",
                "tools/diamond_tiling/run_pluto_diamond_suite.py",
                "tools/parallel_current/run_parallel_current_suite.py",
                "tools/vector_current/run_vector_current_suite.py",
                "tools/tiling_routes/check_complete_direct_routes.py",
                "tools/tiling_routes/check_scalar_interleaved_fusion.py",
                "tools/tiling_routes/check_non_second_level_routes.py",
                "tools/tiling_routes/test_route_telemetry.py",
                "tools/polopt_flag_suites/manifest_runner.py",
                "tools/polopt_flag_suites/test_manifest_runner.py",
                "tools/polopt_flag_suites/pluto_compat_driver.py",
                "tools/polopt_flag_suites/run_pluto_compat_suite.py",
                "tools/second_level_tiling/check_second_level_diamond_routes.py",
                "tools/second_level_tiling/check_scheduler_flag_forwarding.py",
                "tools/second_level_tiling/check_standalone_formal_route.py",
                "tools/second_level_tiling/check_suite_manifest.py",
                "tools/second_level_tiling/run_second_level_tile_suite.py",
            ],
            60,
        ),
        (
            "artifact-runner-timeout-unit",
            [
                sys.executable,
                "tools/artifact/test_artifact_runner_timeout.py",
            ],
            60,
        ),
        (
            "tiling-route-summary-unit",
            [
                sys.executable,
                "tools/artifact/test_tiling_route_summary.py",
            ],
            60,
        ),
        (
            "release-provenance-unit",
            [
                sys.executable,
                "tools/artifact/test_release_provenance.py",
            ],
            60,
        ),
        (
            "manifest-runner-fail-closed-unit",
            [
                sys.executable,
                "tools/polopt_flag_suites/test_manifest_runner.py",
            ],
            60,
        ),
        (
            "tiling-route-telemetry-unit",
            [
                sys.executable,
                "tools/tiling_routes/test_route_telemetry.py",
            ],
            60,
        ),
        (
            "unrolljam-route-guard-unit",
            [
                sys.executable,
                "tools/artifact/test_unrolljam_route_guard.py",
            ],
            60,
        ),
        (
            "extracted-zero-fallback-gate",
            [
                "opam",
                "exec",
                "--",
                "make",
                "-f",
                "Makefile.extr",
                "test-extracted-zero-fallback",
            ],
            180,
        ),
        (
            "proof-report",
            [
                sys.executable,
                "tools/artifact/proof_report.py",
                "--json-out",
                str(out_dir / "proof-report.json"),
                "--markdown-out",
                str(out_dir / "proof-report.md"),
            ],
            60,
        ),
        (
            "capability-matrix",
            [
                sys.executable,
                "tools/artifact/generate_capability_matrix.py",
                "--json-out",
                str(out_dir / "capability-matrix.json"),
                "--markdown-out",
                str(out_dir / "capability-matrix.md"),
            ],
            60,
        ),
        (
            "codegen-gap-exploration",
            [
                sys.executable,
                "tools/artifact/explore_codegen_gaps.py",
                "--output-root",
                str(out_dir / "codegen-gaps"),
            ],
            60,
        ),
        (
            "unrolljam-effect-corpus",
            [
                sys.executable,
                "tools/artifact/explore_unrolljam_effect_corpus.py",
                "--output-root",
                str(out_dir / "unrolljam-effect-corpus"),
            ],
            180,
        ),
        (
            "identity-composition-exploration",
            identity_composition_command,
            900,
        ),
        (
            "direct-only-tiling-route-smoke",
            [
                sys.executable,
                "tools/tiling_routes/check_complete_direct_routes.py",
                "--polopt",
                "./polopt",
                "--polcert",
                "./polcert",
                "--timeout",
                "180",
            ],
            900,
        ),
        (
            "scalar-interleaved-tiling-route",
            [
                sys.executable,
                "tools/tiling_routes/check_scalar_interleaved_fusion.py",
                "--polcert",
                "./polcert",
                "--timeout",
                "60",
            ],
            120,
        ),
        (
            "non-second-level-tiling-routes",
            [
                sys.executable,
                "tools/tiling_routes/check_non_second_level_routes.py",
                "--polopt",
                "./polopt",
                "--timeout",
                "180",
            ],
            900,
        ),
        (
            "pluto-compat-suite",
            [
                sys.executable,
                "tools/polopt_flag_suites/run_pluto_compat_suite.py",
                "--timeout",
                "30",
            ],
            900,
        ),
        (
            "end-to-end-c-const-unroll",
            [
                sys.executable,
                "tools/end_to_end_c/run_case.py",
                "tests/end-to-end-c/cases/const_unroll",
                "--polopt",
                "./polopt",
                "--output-root",
                str(out_dir / "end-to-end-c"),
                "--benchmark-repeats",
                "1",
            ],
            120,
        ),
        (
            "end-to-end-c-unrolljam-block-variable",
            [
                sys.executable,
                "tools/end_to_end_c/run_case.py",
                "tests/end-to-end-c/cases/unrolljam_block_variable",
                "--polopt",
                "./polopt",
                "--output-root",
                str(out_dir / "end-to-end-c"),
                "--benchmark-repeats",
                "1",
            ],
            120,
        ),
        (
            "end-to-end-c-unrolljam-dependent-guard",
            [
                sys.executable,
                "tools/end_to_end_c/run_case.py",
                "tests/end-to-end-c/cases/unrolljam_dependent_guard",
                "--polopt",
                "./polopt",
                "--output-root",
                str(out_dir / "end-to-end-c"),
                "--benchmark-repeats",
                "1",
            ],
            120,
        ),
        (
            "end-to-end-c-stride-even",
            [
                sys.executable,
                "tools/end_to_end_c/run_case.py",
                "tests/end-to-end-c/cases/stride_even",
                "--polopt",
                "./polopt",
                "--output-root",
                str(out_dir / "end-to-end-c"),
                "--benchmark-repeats",
                "1",
            ],
            120,
        ),
        (
            "end-to-end-c-stride-down",
            [
                sys.executable,
                "tools/end_to_end_c/run_case.py",
                "tests/end-to-end-c/cases/stride_down",
                "--polopt",
                "./polopt",
                "--output-root",
                str(out_dir / "end-to-end-c"),
                "--benchmark-repeats",
                "1",
            ],
            120,
        ),
        (
            "second-level-scheduler-forwarding",
            [
                sys.executable,
                "tools/second_level_tiling/check_scheduler_flag_forwarding.py",
            ],
            60,
        ),
        (
            "second-level-suite",
            [
                sys.executable,
                "tools/second_level_tiling/run_second_level_tile_suite.py",
                "--polopt",
                "./polopt",
                "--timeout",
                "180",
            ],
            1800,
        ),
        (
            "diamond-suite",
            [
                sys.executable,
                "tools/diamond_tiling/run_pluto_diamond_suite.py",
                "--timeout-seconds",
                str(diamond_timeout),
                "--output-root",
                str(out_dir / "diamond-suite"),
            ],
            max(600, diamond_timeout * 20),
        ),
    ]


def full_checks() -> list[tuple[str, list[str], int | None]]:
    return [
        (
            "check-admitted",
            ["opam", "exec", "--", "make", "-s", "check-admitted"],
            120,
        ),
        (
            "strict-loop-suite",
            ["opam", "exec", "--", "make", "test-polopt-loop-suite"],
            None,
        ),
        (
            "iss-suite",
            ["opam", "exec", "--", "make", "test-iss-pluto-suite"],
            None,
        ),
        (
            "parallel-current-suite",
            ["opam", "exec", "--", "make", "test-parallel-current-suite"],
            None,
        ),
        (
            "vector-current-suite",
            ["opam", "exec", "--", "make", "test-vector-current-suite"],
            None,
        ),
    ]


def extended_checks(out_dir: Path) -> list[tuple[str, list[str], int | None]]:
    return [
        (
            "flag-effect-exploration",
            [
                sys.executable,
                "tools/artifact/explore_flag_effects.py",
                "--json-out",
                str(out_dir / "flag-effects.json"),
                "--markdown-out",
                str(out_dir / "flag-effects.md"),
                "--limit-per-pair",
                "2",
                "--timeout",
                "20",
            ],
            1800,
        )
    ]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["smoke", "full", "extended"], default="smoke")
    ap.add_argument("--output-root", default="/tmp/polcert-artifact-check")
    ap.add_argument("--diamond-timeout-seconds", type=int, default=180)
    args = ap.parse_args()

    out_dir = Path(args.output_root).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    environment = collect_environment()
    provenance = read_build_provenance()
    provenance_errors = check_build_provenance(environment, provenance)
    provenance_required = environment["POLCERT_REQUIRE_PROVENANCE"] == "1"
    if provenance_errors:
        summary = {
            "root": str(ROOT),
            "mode": args.mode,
            "output_root": str(out_dir),
            "environment": environment,
            "build_provenance": {
                "required": provenance_required,
                "manifest_present": provenance is not None,
                "manifest": provenance,
                "verified": False,
                "errors": provenance_errors,
            },
            "results": [],
            "ok": False,
        }
        (out_dir / "artifact-results.json").write_text(
            json.dumps(summary, indent=2, sort_keys=True)
        )
        for error in provenance_errors:
            print(f"[artifact-check] provenance error: {error}", file=sys.stderr)
        return 2

    # Smoke mode is for artifact health checks, not for exhaustive route search.
    # Full/extended modes keep the unbounded identity-composition exploration.
    identity_composition_limits = (16, 16) if args.mode == "smoke" else None
    checks = base_checks(out_dir, args.diamond_timeout_seconds, identity_composition_limits)
    if args.mode in ("full", "extended"):
        checks.extend(full_checks())
    if args.mode == "extended":
        checks.extend(extended_checks(out_dir))

    results: list[CheckResult] = []
    for name, command, timeout in checks:
        print(f"[artifact-check] {name}: running")
        result = run_check(name, command, out_dir, timeout)
        results.append(result)
        status = "PASS" if result.ok else f"FAIL exit={result.returncode}"
        print(f"[artifact-check] {name}: {status} ({result.elapsed_seconds:.1f}s)")
        if not result.ok:
            break

    summary = {
        "root": str(ROOT),
        "mode": args.mode,
        "output_root": str(out_dir),
        "environment": environment,
        "build_provenance": {
            "required": provenance_required,
            "manifest_present": provenance is not None,
            "manifest": provenance,
            "verified": provenance_required and not provenance_errors,
            "errors": provenance_errors,
        },
        "results": [dict(asdict(item), ok=item.ok) for item in results],
        "ok": all(item.ok for item in results),
    }
    route_summary = build_tiling_route_summary(results)
    route_summary_path = out_dir / "tiling-route-summary.json"
    route_summary_path.write_text(
        json.dumps(route_summary, indent=2, sort_keys=True), encoding="utf-8"
    )
    summary["tiling_route_summary"] = {
        "path": str(route_summary_path),
        "verified": route_summary["verified"],
    }
    summary["ok"] = bool(
        summary["ok"] and route_summary["verified"] and not provenance_errors
    )
    (out_dir / "artifact-results.json").write_text(json.dumps(summary, indent=2, sort_keys=True))
    print(f"[artifact-check] summary: {out_dir / 'artifact-results.json'}")
    return 0 if summary["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
