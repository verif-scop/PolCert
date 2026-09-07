#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib
import re
import subprocess


ROOT = pathlib.Path(__file__).resolve().parents[2]
OPTIMIZED_LOOP_MARKER = "== Optimized Loop =="


def load_manifest(path: pathlib.Path) -> dict[str, object]:
    data = json.loads(path.read_text())
    if not isinstance(data, dict):
        raise SystemExit(f"manifest must be a JSON object: {path}")
    return data


def load_fixture_map(manifest_path: pathlib.Path, data: dict[str, object]) -> dict[str, pathlib.Path]:
    raw_fixtures = data.get("fixtures", {})
    if not isinstance(raw_fixtures, dict):
        raise SystemExit("fixtures must be an object mapping names to relative paths")
    fixtures: dict[str, pathlib.Path] = {}
    for name, relpath in raw_fixtures.items():
        if not isinstance(name, str) or not isinstance(relpath, str):
            raise SystemExit("fixtures must map string names to string paths")
        fixture_path = (manifest_path.parent / relpath).resolve()
        if not fixture_path.is_file():
            raise SystemExit(f"fixture not found: {fixture_path}")
        fixtures[name] = fixture_path
    return fixtures


def run_polopt(
    polopt: pathlib.Path,
    input_paths: list[pathlib.Path],
    args: list[str],
    timeout: int | None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(polopt), *args, *(str(path) for path in input_paths)],
        cwd=str(ROOT),
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )


def optimized_loop(stdout: str) -> str | None:
    pos = stdout.find(OPTIMIZED_LOOP_MARKER)
    if pos < 0:
        return None
    return stdout[pos:]


def string_list_field(spec: dict[str, object], field: str) -> list[str]:
    raw = spec.get(field, [])
    if not isinstance(raw, list) or not all(isinstance(item, str) for item in raw):
        raise SystemExit(f"{spec.get('name', '<unnamed>')}: {field} must be a string list")
    return list(raw)


def args_list_field(spec: dict[str, object], field: str) -> list[str] | None:
    raw = spec.get(field)
    if raw is None:
        return None
    if not isinstance(raw, list) or not all(isinstance(item, str) for item in raw):
        raise SystemExit(f"{spec.get('name', '<unnamed>')}: {field} must be a string list")
    return list(raw)


def input_paths_field(
    fixtures: dict[str, pathlib.Path],
    spec: dict[str, object],
) -> list[pathlib.Path]:
    raw_input_fixtures = spec.get("input_fixtures")
    if raw_input_fixtures is None:
        raw_input_fixtures = [spec.get("fixture")]
    if (
        not isinstance(raw_input_fixtures, list)
        or not raw_input_fixtures
        or not all(isinstance(name, str) for name in raw_input_fixtures)
    ):
        raise SystemExit(
            f"{spec.get('name', '<unnamed>')}: input_fixtures must be a nonempty string list"
        )
    paths: list[pathlib.Path] = []
    for fixture_name in raw_input_fixtures:
        if fixture_name not in fixtures:
            raise SystemExit(
                f"{spec.get('name', '<unnamed>')}: unknown fixture {fixture_name!r}"
            )
        paths.append(fixtures[fixture_name])
    return paths


def string_count_field(spec: dict[str, object], field: str) -> dict[str, int]:
    raw = spec.get(field, {})
    if not isinstance(raw, dict):
        raise SystemExit(f"{spec.get('name', '<unnamed>')}: {field} must be an object")
    counts: dict[str, int] = {}
    for needle, count in raw.items():
        if not isinstance(needle, str) or not isinstance(count, int) or count < 0:
            raise SystemExit(
                f"{spec.get('name', '<unnamed>')}: {field} must map strings to nonnegative integers"
            )
        counts[needle] = count
    return counts


def evaluate_check(
    fixtures: dict[str, pathlib.Path],
    polopt: pathlib.Path,
    spec: dict[str, object],
    *,
    stderr_needles_exactly_once: bool,
    timeout: int | None,
) -> str | None:
    if not isinstance(spec.get("name"), str):
        raise SystemExit("check name must be a string")
    if "input_fixtures" not in spec and not isinstance(spec.get("fixture"), str):
        raise SystemExit(
            f"{spec.get('name', '<unnamed>')}: fixture must be a string"
        )
    if not isinstance(spec.get("expect"), str):
        raise SystemExit(f"{spec.get('name', '<unnamed>')}: expect must be a string")
    if "needle" in spec and not isinstance(spec.get("needle"), str):
        raise SystemExit(f"{spec.get('name', '<unnamed>')}: needle must be a string")
    raw_args = spec.get("args", [])
    if not isinstance(raw_args, list) or not all(isinstance(arg, str) for arg in raw_args):
        raise SystemExit(f"{spec['name']}: args must be a string list")
    input_paths = input_paths_field(fixtures, spec)

    try:
        proc = run_polopt(polopt, input_paths, list(raw_args), timeout)
    except subprocess.TimeoutExpired:
        return f"{spec['name']}: command timed out after {timeout} seconds"
    expected = str(spec["expect"])
    needles = []
    if "needle" in spec:
        needles.append(str(spec["needle"]))
    needles.extend(string_list_field(spec, "needles"))
    stdout_regexes = string_list_field(spec, "stdout_regexes")
    absent_needles = string_list_field(spec, "absent_needles")
    stdout_min_counts = string_count_field(spec, "stdout_min_counts")
    stderr_needles = string_list_field(spec, "stderr_needles")
    stderr_absent_needles = string_list_field(spec, "stderr_absent_needles")
    stderr_counts = string_count_field(spec, "stderr_counts")
    differs_from_args = args_list_field(spec, "differs_from_args")
    if expected == "success":
        if proc.returncode != 0:
            return f"{spec['name']}: expected success, got exit {proc.returncode}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        optimized = optimized_loop(proc.stdout)
        if optimized is None:
            return (
                f"{spec['name']}: successful optimization omitted the final optimized-loop section"
                f"\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        for needle in needles:
            if needle not in optimized:
                return f"{spec['name']}: missing {needle!r} in stdout\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        for pattern in stdout_regexes:
            if re.search(pattern, optimized) is None:
                return f"{spec['name']}: missing stdout pattern {pattern!r}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        for needle in absent_needles:
            if needle in optimized:
                return f"{spec['name']}: unexpected {needle!r} in stdout\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        for needle, minimum in stdout_min_counts.items():
            actual = optimized.count(needle)
            if actual < minimum:
                return (
                    f"{spec['name']}: expected at least {minimum} occurrences of {needle!r} "
                    f"in stdout, found {actual}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
        for needle in stderr_needles:
            if needle not in proc.stderr:
                return f"{spec['name']}: missing {needle!r} in stderr\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            if stderr_needles_exactly_once:
                actual_count = proc.stderr.count(needle)
                if actual_count != 1:
                    return (
                        f"{spec['name']}: expected exactly one occurrence of {needle!r} "
                        f"in stderr, got {actual_count}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                    )
        expected_route_lines = [
            needle
            for needle in stderr_needles
            if needle.startswith("[tiling-validation] route=")
        ]
        if stderr_needles_exactly_once and expected_route_lines:
            actual_route_lines = [
                line.strip()
                for line in proc.stderr.splitlines()
                if line.strip().startswith("[tiling-validation] route=")
            ]
            if actual_route_lines != expected_route_lines:
                return (
                    f"{spec['name']}: expected complete route list "
                    f"{expected_route_lines!r}, got {actual_route_lines!r}"
                    f"\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
        for needle in stderr_absent_needles:
            if needle in proc.stderr:
                return f"{spec['name']}: unexpected {needle!r} in stderr\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        for needle, expected_count in stderr_counts.items():
            actual_count = proc.stderr.count(needle)
            if actual_count != expected_count:
                return (
                    f"{spec['name']}: expected {expected_count} occurrences of {needle!r} "
                    f"in stderr, got {actual_count}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
        if differs_from_args is not None:
            try:
                baseline = run_polopt(polopt, input_paths, differs_from_args, timeout)
            except subprocess.TimeoutExpired:
                return f"{spec['name']}: baseline command timed out after {timeout} seconds"
            if baseline.returncode != 0:
                return (
                    f"{spec['name']}: baseline command failed with exit {baseline.returncode}\n"
                    f"baseline stdout:\n{baseline.stdout}\nbaseline stderr:\n{baseline.stderr}"
                )
            baseline_optimized = optimized_loop(baseline.stdout)
            if baseline_optimized is None:
                return (
                    f"{spec['name']}: baseline command omitted the optimized-loop section"
                    f"\nbaseline stdout:\n{baseline.stdout}\nbaseline stderr:\n{baseline.stderr}"
                )
            if baseline_optimized == optimized:
                return (
                    f"{spec['name']}: stdout did not differ from baseline args {differs_from_args!r}\n"
                    f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
        return None
    if expected == "failure":
        if proc.returncode == 0:
            return f"{spec['name']}: expected failure, but command succeeded\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        if optimized_loop(proc.stdout) is not None:
            return (
                f"{spec['name']}: failed command emitted an optimized-loop section"
                f"\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        haystack = proc.stderr + proc.stdout
        for needle in needles:
            if needle not in haystack:
                return f"{spec['name']}: missing {needle!r} in failure output\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            if (
                stderr_needles_exactly_once
                and needle.startswith("[vector-validation]")
                and proc.stderr.count(needle) != 1
            ):
                return (
                    f"{spec['name']}: expected exactly one occurrence of {needle!r} "
                    f"in failure stderr\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
        for needle in absent_needles:
            if needle in haystack:
                return f"{spec['name']}: unexpected {needle!r} in failure output\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        for needle in stderr_absent_needles:
            if needle in proc.stderr:
                return f"{spec['name']}: unexpected {needle!r} in failure stderr\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        for needle, expected_count in stderr_counts.items():
            actual_count = proc.stderr.count(needle)
            if actual_count != expected_count:
                return (
                    f"{spec['name']}: expected {expected_count} occurrences of {needle!r} "
                    f"in failure stderr, got {actual_count}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
        return None
    raise SystemExit(f"{spec['name']}: unsupported expect value {expected!r}")


def expectation_summary(spec: dict[str, object]) -> str:
    expected = str(spec.get("expect", "invalid"))
    marker_count = (
        (1 if "needle" in spec else 0)
        + len(string_list_field(spec, "needles"))
        + len(string_list_field(spec, "stdout_regexes"))
        + len(string_list_field(spec, "absent_needles"))
        + len(string_count_field(spec, "stdout_min_counts"))
        + len(string_list_field(spec, "stderr_needles"))
        + len(string_list_field(spec, "stderr_absent_needles"))
        + len(string_count_field(spec, "stderr_counts"))
    )
    differs = args_list_field(spec, "differs_from_args") is not None
    return (
        f"result={expected},markers={marker_count},"
        f"baseline-difference={str(differs).lower()}"
    )


def effect_assertion_count(spec: dict[str, object]) -> int:
    if spec.get("expect") != "success":
        return 0
    return (
        (1 if "needle" in spec else 0)
        + len(string_list_field(spec, "needles"))
        + len(string_list_field(spec, "stdout_regexes"))
        + len(string_list_field(spec, "absent_needles"))
        + len(string_count_field(spec, "stdout_min_counts"))
        + (1 if args_list_field(spec, "differs_from_args") is not None else 0)
    )


def run_manifest_suite(*, manifest_path: pathlib.Path, polopt: pathlib.Path) -> int:
    data = load_manifest(manifest_path)
    suite_name = data.get("suite_name", "POLOPT-FLAG-SUITE")
    if not isinstance(suite_name, str):
        raise SystemExit("suite_name must be a string")
    stderr_needles_exactly_once = data.get("stderr_needles_exactly_once", False)
    if not isinstance(stderr_needles_exactly_once, bool):
        raise SystemExit("stderr_needles_exactly_once must be a boolean")
    timeout = data.get("timeout_seconds")
    if timeout is not None and (not isinstance(timeout, int) or timeout < 1):
        raise SystemExit("timeout_seconds must be a positive integer")
    raw_checks = data.get("checks", [])
    if not isinstance(raw_checks, list) or not all(isinstance(spec, dict) for spec in raw_checks):
        raise SystemExit("checks must be a list of objects")

    fixtures = load_fixture_map(manifest_path, data)
    failures: list[str] = []
    for spec in raw_checks:
        failure = evaluate_check(
            fixtures,
            polopt,
            spec,
            stderr_needles_exactly_once=stderr_needles_exactly_once,
            timeout=timeout,
        )
        if failure is not None:
            failures.append(failure)
        effect_assertions = effect_assertion_count(spec)
        coverage = (
            "effect"
            if effect_assertions > 0
            else "rejection-contract"
            if spec.get("expect") == "failure"
            else "acceptance-only"
        )
        if failure is not None:
            interpretation = "requested-result-or-effect-was-not-observed"
        elif coverage == "effect":
            interpretation = "requested-result-and-effects-observed"
        elif coverage == "rejection-contract":
            interpretation = "unsupported-route-rejected-as-declared"
        else:
            interpretation = "route-accepted-no-specific-effect-asserted"
        print(
            f"[{suite_name}] {'PASS' if failure is None else 'FAIL'} "
            f"case={spec.get('name', '<unnamed>')} "
            f"expected={expectation_summary(spec)} "
            f"coverage={coverage} "
            f"actual={'all-declared-assertions-matched' if failure is None else 'assertion-mismatch'} "
            f"interpretation={interpretation}"
        )

    if failures:
        print(f"[{suite_name}] FAIL")
        for failure in failures:
            print(failure)
        return 1

    print(
        f"[{suite_name}] PASS expected={len(raw_checks)} actual={len(raw_checks)} "
        "interpretation=all-manifest-contracts-matched"
    )
    return 0
