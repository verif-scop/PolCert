#!/usr/bin/env python3
"""Check malformed tilings and distinguish failures in later consumers."""

from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path
import subprocess


REJECTED_ROUTE = "[tiling-validation] route=rejected"
BAND_ROUTE = "[tiling-validation] route=permutable-band"
VECTOR_HINT_SKIPPED = (
    "[vector-validation] status=skipped "
    "reason=hint-not-certifiable-or-non-innermost"
)
PARALLEL_REJECTION = (
    "[parallel-validation] status=rejected source=explicit-current "
    "reason=not-certifiable-or-out-of-range"
)
VECTOR_REJECTION = (
    "[vector-validation] status=rejected source=explicit-current "
    "reason=not-certifiable-or-non-innermost"
)
TILE_LINK_MUTATION = "[rejecting-pluto] corrupted one tiling tile-link"
FINAL_AFFINE_MUTATION = "[rejecting-pluto] reversed "


@dataclass(frozen=True)
class MalformedTilingCase:
    name: str
    fixture: Path
    args: tuple[str, ...]


@dataclass(frozen=True)
class ConsumerFailureCase:
    name: str
    fixture: Path
    args: tuple[str, ...]
    rejection: str


def route_lines(stderr: str) -> list[str]:
    return [
        line.strip()
        for line in stderr.splitlines()
        if line.strip().startswith("[tiling-validation] route=")
    ]


def hinted_malformed_rejection_stage(
    consumer: str, stderr: str, *, reader_rejection_confirmed: bool = False,
) -> str | None:
    """Keep formal tiling rejection separate from strict proposal preflight."""
    routes = route_lines(stderr)
    if routes == [REJECTED_ROUTE] and not any(marker in stderr for marker in (
        "[parallel-validation] status=rejected", "[vector-validation] status=rejected",
    )):
        return "tiling"
    if (consumer == "parallel-strict" and not routes
            and "[parallel-validation] proposal=actual reason=no-compatible-candidate" in stderr
            and "[parallel-validation] status=rejected source=pluto-hint reason=no-certifiable-dimension" in stderr
            and "[vector-validation] status=rejected" not in stderr):
        if "[parallel-validation] proposal=actual reason=instance-space-mismatch" in stderr:
            return "parallel-preflight"
        if reader_rejection_confirmed:
            return "parallel-reader"
    return None


def confirm_second_level_reader_rejection(root: Path, stderr: str, timeout: int) -> bool:
    """Re-read this run's exact corrupted proposals; no formal rejection is inferred."""
    prefix = TILE_LINK_MUTATION + " in "
    names = [line.split(prefix, 1)[1].strip() for line in stderr.splitlines() if prefix in line]
    if not names:
        return False
    for name in dict.fromkeys(names):
        if Path(name).name != name or not name.endswith(".posttile.scop"):
            return False
        after = root / name
        before = root / name[:-len(".posttile.scop")]
        before = Path(str(before) + ".midtransform.scop")
        if not before.is_file() or not after.is_file():
            return False
        proc = subprocess.run(
            [str(root / "polcert"), "--tiling", "--second-level-tile", str(before), str(after)],
            cwd=root, text=True, capture_output=True, timeout=timeout, check=False,
        )
        if (proc.returncode != 2 or "cannot extract tiling witness" not in proc.stderr
                or "incomplete tile-link pair" not in proc.stderr
                or route_lines(proc.stderr) or "[TILING-" in proc.stdout + proc.stderr):
            return False
        print(f"[malformed-reader] before={before.name} after={after.name} exit=2 reason=incomplete-tile-link-pair", flush=True)
    return True


def final_affine_rejection_stage(consumer: str, stderr: str) -> str | None:
    routes = route_lines(stderr)
    if routes == [BAND_ROUTE] and not any(marker in stderr for marker in (
        "[parallel-validation] status=rejected", "[vector-validation] status=rejected",
    )):
        return "final-affine"
    if (consumer == "parallel-hint-strict" and not routes
            and "[parallel-validation] scope=phase reason=affine-rejected" in stderr
            and "[parallel-validation] proposal=actual coordinate=" in stderr
            and " accepted=false nontrivial=false" in stderr
            and "[parallel-validation] status=rejected source=pluto-hint reason=no-certifiable-dimension" in stderr
            and "[vector-validation] status=rejected" not in stderr):
        return "parallel-candidate-affine"
    return None


def run_polopt(
    *,
    polopt: Path,
    fixture: Path,
    args: tuple[str, ...],
    timeout: int,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(polopt), *args, str(fixture)],
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
        env=os.environ.copy() if env is None else env,
    )


def malformed_tiling_cases(root: Path) -> list[MalformedTilingCase]:
    symbolic = root / "tools" / "second_level_tiling" / "fixtures" / "symbolic-independent-2d.loop"
    mixed_depth = root / "tools" / "second_level_tiling" / "fixtures" / "matmul-init.loop"
    diamond = (
        root
        / "tools"
        / "parallel_current"
        / "fixtures"
        / "diamond-example-inner-batch.loop"
    )
    cases: list[MalformedTilingCase] = []
    for name, fixture, args in (
        ("ordinary", symbolic, ()),
        ("identity-mixed-depth", mixed_depth, ("--identity-tiled",)),
        ("second-level", symbolic, ("--second-level-tile",)),
        (
            "second-level-identity-mixed-depth",
            mixed_depth,
            ("--second-level-tile", "--identity-tiled"),
        ),
        ("diamond", diamond, ("--diamond-tile",)),
        ("full-diamond", diamond, ("--full-diamond-tile",)),
        (
            "second-level-diamond",
            diamond,
            ("--second-level-tile", "--diamond-tile"),
        ),
        (
            "second-level-full-diamond",
            diamond,
            ("--second-level-tile", "--full-diamond-tile"),
        ),
    ):
        cases.append(MalformedTilingCase(name, fixture, args))
        cases.append(MalformedTilingCase(f"{name}-iss", fixture, (*args, "--iss")))
    return cases


def consumer_failure_cases(root: Path) -> list[ConsumerFailureCase]:
    symbolic = root / "tools" / "second_level_tiling" / "fixtures" / "symbolic-independent-2d.loop"
    mixed_depth = root / "tools" / "second_level_tiling" / "fixtures" / "matmul-init.loop"
    diamond = (
        root
        / "tools"
        / "parallel_current"
        / "fixtures"
        / "diamond-example-inner-batch.loop"
    )
    producers = (
        ("ordinary", symbolic, ()),
        ("second-level-iss", symbolic, ("--second-level-tile", "--iss")),
        ("identity-mixed-depth", mixed_depth, ("--identity-tiled",)),
        (
            "second-level-identity-mixed-depth-iss",
            mixed_depth,
            ("--second-level-tile", "--identity-tiled", "--iss"),
        ),
        ("diamond", diamond, ("--diamond-tile",)),
        ("full-diamond-iss", diamond, ("--full-diamond-tile", "--iss")),
    )
    cases: list[ConsumerFailureCase] = []
    for name, fixture, producer_args in producers:
        cases.append(
            ConsumerFailureCase(
                f"{name}-parallel-current",
                fixture,
                (*producer_args, "--parallel-current", "999"),
                PARALLEL_REJECTION,
            )
        )
        cases.append(
            ConsumerFailureCase(
                f"{name}-vector-current",
                fixture,
                (*producer_args, "--vector-current", "999"),
                VECTOR_REJECTION,
            )
        )
    return cases


def assert_no_alternate_route(label: str, stderr: str) -> None:
    if BAND_ROUTE in stderr:
        raise AssertionError(f"{label} malformed candidate reported permutable-band")
    if "fallback" in stderr.lower():
        raise AssertionError(f"{label} reported a forbidden fallback route")
    if "plain tiling producer changed the post-tile schedule" in stderr:
        raise AssertionError(f"{label} failed at phase consistency, not tiling validation")


def check_malformed_tiling_cases(
    *,
    polopt: Path,
    wrapper: Path,
    real_pluto: Path,
    root: Path,
    timeout: int,
) -> int:
    env = os.environ.copy()
    env["POLCERT_REAL_PLUTO"] = str(real_pluto)
    env["POLCERT_PLUTO"] = str(wrapper)
    env["POLCERT_REJECTING_PLUTO_MODE"] = "tiling"
    cases = malformed_tiling_cases(root)
    for case in cases:
        proc = run_polopt(
            polopt=polopt,
            fixture=case.fixture,
            args=case.args,
            timeout=timeout,
            env=env,
        )
        label = f"malformed {case.name}"
        if proc.returncode == 0:
            raise AssertionError(
                f"{label} did not fail closed\n"
                f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        if route_lines(proc.stderr) != [REJECTED_ROUTE]:
            raise AssertionError(
                f"{label} did not report exactly one rejected tiling route\n"
                f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        assert_no_alternate_route(label, proc.stderr)
        if proc.stderr.count(TILE_LINK_MUTATION) != 1:
            raise AssertionError(f"{label} did not perform exactly one tile-link mutation")
        if proc.stderr.count("[alarm]") != 1:
            raise AssertionError(f"{label} did not report exactly one rejection alarm")
        if "== Optimized Loop ==" in proc.stdout:
            raise AssertionError(f"{label} emitted output after rejecting tiling")
    return len(cases)


def check_integrated_direct_checker_rejection(
    *,
    polopt: Path,
    real_pluto: Path,
    root: Path,
    timeout: int,
) -> None:
    env = os.environ.copy()
    env["POLCERT_REAL_PLUTO"] = str(real_pluto)
    env["POLCERT_PLUTO"] = str(
        root / "tools" / "tiling_routes" / "frozen_nonpermutable_pluto.py"
    )
    proc = run_polopt(
        polopt=polopt,
        fixture=(
            root
            / "tools"
            / "tiling_routes"
            / "fixtures"
            / "nonpermutable-band.loop"
        ),
        args=(),
        timeout=timeout,
        env=env,
    )
    label = "integrated direct-checker nonpermutable band"
    if proc.returncode == 0:
        raise AssertionError(f"{label} unexpectedly succeeded")
    if route_lines(proc.stderr) != [REJECTED_ROUTE]:
        raise AssertionError(
            f"{label} did not report exactly one rejected route\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    for phase in ("affine", "tiled"):
        if proc.stderr.count(f"[frozen-nonpermutable-pluto] phase={phase} ") != 1:
            raise AssertionError(f"{label} did not replace the {phase} phase")
    if ".posttile.scop," not in proc.stderr or ".afterscheduling.scop with nonpermutable-band.posttile.scop" not in proc.stderr:
        raise AssertionError(f"{label} did not bind the tiled and final phase outputs")
    if "plain tiling producer changed the post-tile schedule" in proc.stderr:
        raise AssertionError(f"{label} failed before reaching tiling validation")
    assert_no_alternate_route(label, proc.stderr)
    if proc.stderr.count("[alarm]") != 1:
        raise AssertionError(f"{label} did not report exactly one alarm")
    if "== Optimized Loop ==" in proc.stdout:
        raise AssertionError(f"{label} emitted output after rejection")


def check_consumer_failure_cases(
    *,
    polopt: Path,
    root: Path,
    timeout: int,
) -> int:
    cases = consumer_failure_cases(root)
    for case in cases:
        proc = run_polopt(
            polopt=polopt,
            fixture=case.fixture,
            args=case.args,
            timeout=timeout,
        )
        label = f"consumer failure {case.name}"
        if proc.returncode == 0:
            raise AssertionError(f"{label} unexpectedly succeeded")
        if route_lines(proc.stderr):
            raise AssertionError(
                f"{label} was mislabeled as a tiling outcome: "
                f"{route_lines(proc.stderr)!r}"
            )
        if proc.stderr.count(case.rejection) != 1:
            raise AssertionError(f"{label} omitted its unique consumer rejection")
        if "fallback" in proc.stderr.lower() or BAND_ROUTE in proc.stderr:
            raise AssertionError(f"{label} leaked an accepted tiling route")
        if proc.stderr.count("[alarm]") != 1:
            raise AssertionError(
                f"{label} reported {proc.stderr.count('[alarm]')} alarms, "
                "expected 1"
            )
        if "== Optimized Loop ==" in proc.stdout:
            raise AssertionError(f"{label} emitted output after rejection")
        if "validation failed" not in proc.stderr.lower():
            raise AssertionError(f"{label} omitted its validation failure")
    return len(cases)


def check_malformed_tiling_with_explicit_consumers(
    *,
    polopt: Path,
    wrapper: Path,
    real_pluto: Path,
    root: Path,
    timeout: int,
) -> int:
    all_cases = {case.name: case for case in malformed_tiling_cases(root)}
    producer_names = (
        "ordinary",
        "identity-mixed-depth-iss",
        "second-level",
        "second-level-identity-mixed-depth-iss",
        "diamond",
        "full-diamond-iss",
        "second-level-diamond",
        "second-level-full-diamond-iss",
    )
    consumers = (
        ("parallel-current", ("--parallel-current", "999"), PARALLEL_REJECTION),
        ("vector-current", ("--vector-current", "999"), VECTOR_REJECTION),
    )
    env = os.environ.copy()
    env["POLCERT_REAL_PLUTO"] = str(real_pluto)
    env["POLCERT_PLUTO"] = str(wrapper)
    env["POLCERT_REJECTING_PLUTO_MODE"] = "tiling"
    count = 0
    for producer_name in producer_names:
        producer = all_cases[producer_name]
        for consumer_name, consumer_args, consumer_rejection in consumers:
            proc = run_polopt(
                polopt=polopt,
                fixture=producer.fixture,
                args=(*producer.args, *consumer_args),
                timeout=timeout,
                env=env,
            )
            label = f"malformed {producer_name} with {consumer_name}"
            if proc.returncode == 0:
                raise AssertionError(f"{label} did not fail closed")
            if route_lines(proc.stderr) != [REJECTED_ROUTE]:
                raise AssertionError(
                    f"{label} did not preserve its unique producer rejection\n"
                    f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
            if consumer_rejection in proc.stderr:
                raise AssertionError(f"{label} was mislabeled as a consumer rejection")
            assert_no_alternate_route(label, proc.stderr)
            if proc.stderr.count(TILE_LINK_MUTATION) != 1:
                raise AssertionError(f"{label} did not mutate exactly one tile link")
            if proc.stderr.count("[alarm]") != 1:
                raise AssertionError(f"{label} did not report exactly one alarm")
            if "== Optimized Loop ==" in proc.stdout:
                raise AssertionError(f"{label} emitted output after rejection")
            count += 1
    return count


def check_malformed_tiling_with_hinted_consumers(
    *,
    polopt: Path,
    wrapper: Path,
    real_pluto: Path,
    root: Path,
    timeout: int,
) -> int:
    all_cases = {case.name: case for case in malformed_tiling_cases(root)}
    producer_names = (
        "ordinary",
        "diamond",
        "second-level-full-diamond-iss",
    )
    consumers = (
        (
            "parallel",
            (
                "--parallel",
                "--innerpar",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
            ),
        ),
        (
            "parallel-strict",
            (
                "--parallel",
                "--parallel-strict",
                "--innerpar",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
            ),
        ),
        (
            "multipar",
            (
                "--parallel",
                "--multipar",
                "--innerpar",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
            ),
        ),
        (
            "multipar-strict",
            (
                "--parallel",
                "--multipar",
                "--parallel-strict",
                "--innerpar",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
            ),
        ),
        (
            "vector",
            (
                "--vector",
                "--smartfuse",
                "--nointratileopt",
                "--nounrolljam",
                "--rar",
                "--noparallel",
            ),
        ),
        (
            "vector-strict",
            (
                "--vector",
                "--vector-strict",
                "--smartfuse",
                "--nointratileopt",
                "--nounrolljam",
                "--rar",
                "--noparallel",
            ),
        ),
    )
    env = os.environ.copy()
    env["POLCERT_REAL_PLUTO"] = str(real_pluto)
    env["POLCERT_PLUTO"] = str(wrapper)
    env["POLCERT_REJECTING_PLUTO_MODE"] = "tiling"
    # The actual-proposal adapter can reject incompatible instance spaces before
    # invoking the formal tiling stage. Its debug marker identifies that boundary.
    env["POLCERT_PARALLEL_DEBUG"] = "1"
    count = 0
    for producer_name in producer_names:
        producer = all_cases[producer_name]
        explicit_phase_args = (
            ()
            if any(
                flag in producer.args
                for flag in ("--diamond-tile", "--full-diamond-tile")
            )
            else ("--nodiamond-tile",)
        )
        for consumer_name, consumer_args in consumers:
            proc = run_polopt(
                polopt=polopt,
                fixture=producer.fixture,
                args=(*producer.args, *consumer_args, *explicit_phase_args),
                timeout=timeout,
                env=env,
            )
            label = f"malformed {producer_name} with hinted {consumer_name}"
            if proc.returncode == 0:
                raise AssertionError(f"{label} did not fail closed")
            stage = hinted_malformed_rejection_stage(consumer_name, proc.stderr)
            if (stage is None and consumer_name == "parallel-strict"
                    and "--second-level-tile" in producer.args):
                stage = hinted_malformed_rejection_stage(
                    consumer_name, proc.stderr,
                    reader_rejection_confirmed=confirm_second_level_reader_rejection(root, proc.stderr, timeout),
                )
            if stage is None:
                raise AssertionError(
                    f"{label} did not fail at a recognized malformed-proposal boundary\n"
                    f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
            assert_no_alternate_route(label, proc.stderr)
            if proc.stderr.count(TILE_LINK_MUTATION) < 1:
                raise AssertionError(f"{label} did not mutate a tile link")
            if proc.stderr.count("[alarm]") != 1:
                raise AssertionError(f"{label} did not report exactly one alarm")
            if "== Optimized Loop ==" in proc.stdout:
                raise AssertionError(f"{label} emitted output after rejection")
            print(f"[malformed-hinted] case={producer_name}/{consumer_name} stage={stage} rejected=true", flush=True)
            count += 1
    return count


def check_final_affine_failure_cases(
    *,
    polopt: Path,
    wrapper: Path,
    real_pluto: Path,
    root: Path,
    timeout: int,
) -> int:
    diamond = (
        root
        / "tools"
        / "parallel_current"
        / "fixtures"
        / "diamond-example-inner-batch.loop"
    )
    producer_cases = (
        ("diamond", ("--diamond-tile",)),
        ("diamond-iss", ("--diamond-tile", "--iss")),
        ("full-diamond", ("--full-diamond-tile",)),
        ("full-diamond-iss", ("--full-diamond-tile", "--iss")),
        (
            "second-level-diamond",
            ("--second-level-tile", "--diamond-tile"),
        ),
        (
            "second-level-diamond-iss",
            ("--second-level-tile", "--diamond-tile", "--iss"),
        ),
        (
            "second-level-full-diamond",
            ("--second-level-tile", "--full-diamond-tile"),
        ),
        (
            "second-level-full-diamond-iss",
            ("--second-level-tile", "--full-diamond-tile", "--iss"),
        ),
    )
    consumers = (
        ("sequential", (), None, 1),
        (
            "parallel-current",
            ("--parallel-current", "0"),
            "[parallel-validation] status=rejected",
            1,
        ),
        (
            "vector-current",
            ("--vector-current", "0"),
            "[vector-validation] status=rejected",
            1,
        ),
        (
            "parallel-hint-strict",
            (
                "--parallel",
                "--parallel-strict",
                "--innerpar",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
            ),
            "[parallel-validation] status=rejected",
            2,
        ),
        (
            "multipar-hint-strict",
            (
                "--parallel",
                "--multipar",
                "--parallel-strict",
                "--innerpar",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
            ),
            "[parallel-validation] status=rejected",
            2,
        ),
        (
            "vector-hint-strict",
            (
                "--vector",
                "--vector-strict",
                "--smartfuse",
                "--nointratileopt",
                "--nounrolljam",
                "--rar",
                "--noparallel",
            ),
            "[vector-validation] status=rejected",
            2,
        ),
    )
    env = os.environ.copy()
    env["POLCERT_REAL_PLUTO"] = str(real_pluto)
    env["POLCERT_PLUTO"] = str(wrapper)
    env["POLCERT_REJECTING_PLUTO_MODE"] = "final-affine"
    env["POLCERT_PARALLEL_DEBUG"] = "1"
    count = 0
    for name, producer_args in producer_cases:
        for (
            consumer_name,
            consumer_args,
            consumer_rejection,
            expected_mutations,
        ) in consumers:
            proc = run_polopt(
                polopt=polopt,
                fixture=diamond,
                args=(*producer_args, *consumer_args),
                timeout=timeout,
                env=env,
            )
            label = f"final affine failure {name} with {consumer_name}"
            if proc.returncode == 0:
                raise AssertionError(
                    f"{label} unexpectedly accepted the malformed final schedule"
                )
            stage = final_affine_rejection_stage(consumer_name, proc.stderr)
            if stage is None:
                raise AssertionError(
                    f"{label} did not report a recognized final-affine rejection\n"
                    f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
            if (stage == "final-affine" and consumer_rejection is not None
                    and consumer_rejection in proc.stderr):
                raise AssertionError(
                    f"{label} was mislabeled as a consumer rejection"
                )
            if REJECTED_ROUTE in proc.stderr or "fallback" in proc.stderr.lower():
                raise AssertionError(f"{label} mislabeled the final affine rejection")
            if proc.stderr.count(FINAL_AFFINE_MUTATION) != expected_mutations:
                raise AssertionError(
                    f"{label} performed "
                    f"{proc.stderr.count(FINAL_AFFINE_MUTATION)} final-schedule "
                    f"mutations, expected {expected_mutations}"
                )
            if proc.stderr.count("[alarm]") != 1:
                raise AssertionError(
                    f"{label} did not report exactly one validation alarm"
                )
            if "== Optimized Loop ==" in proc.stdout:
                raise AssertionError(
                    f"{label} emitted output after a validation alarm"
                )
            print(f"[final-affine-negative] case={name}/{consumer_name} stage={stage} rejected=true", flush=True)
            count += 1
    return count


def check_rejected_tiling_route(
    *,
    polopt: Path,
    fixture: Path,
    timeout: int,
) -> None:
    root = Path(__file__).resolve().parents[2]
    wrapper = Path(__file__).resolve().with_name("rejecting_pluto.py")
    real_pluto = Path(
        os.environ.get(
            "POLCERT_REAL_PLUTO",
            os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"),
        )
    ).resolve()
    if not fixture.is_file():
        raise AssertionError(f"missing legacy rejection fixture: {fixture}")

    malformed_count = check_malformed_tiling_cases(
        polopt=polopt,
        wrapper=wrapper,
        real_pluto=real_pluto,
        root=root,
        timeout=timeout,
    )
    check_integrated_direct_checker_rejection(
        polopt=polopt,
        real_pluto=real_pluto,
        root=root,
        timeout=timeout,
    )

    scalar_only = subprocess.run(
        [
            str(polopt),
            "--second-level-tile",
            str(root / "tests" / "polopt-regression" / "inputs" / "noloop.loop"),
        ],
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
        env=os.environ.copy(),
    )
    if scalar_only.returncode == 0:
        raise AssertionError("scalar-only tiling request did not fail closed")
    if route_lines(scalar_only.stderr) != [REJECTED_ROUTE]:
        raise AssertionError(
            "a tiling request with no non-scalar statement was not explicitly rejected"
        )
    if scalar_only.stderr.count("[alarm]") != 1:
        raise AssertionError("scalar-only rejection omitted its unique alarm")
    if "== Optimized Loop ==" in scalar_only.stdout:
        raise AssertionError("scalar-only rejection emitted optimized output")

    strict_fixture = root / "tools" / "second_level_tiling" / "fixtures" / "matmul-init.loop"
    for second_level in (False, True):
        for use_iss in (False, True):
            args = ["--identity", "--tile"]
            if second_level:
                args.append("--second-level-tile")
            if use_iss:
                args.append("--iss")
            args.extend(
                (
                    "--vector",
                    "--vector-strict",
                    "--nointratileopt",
                    "--nounrolljam",
                    "--nodiamond-tile",
                    "--noparallel",
                    str(strict_fixture),
                )
            )
            strict = subprocess.run(
                [str(polopt), *args],
                text=True,
                capture_output=True,
                timeout=timeout,
                check=False,
                env=os.environ.copy(),
            )
            label = (
                f"{'second-level ' if second_level else ''}"
                f"identity vector-strict{' ISS' if use_iss else ''}"
            )
            if strict.returncode != 0:
                raise AssertionError(f"{label} conservative vector skip failed")
            if route_lines(strict.stderr) != [BAND_ROUTE]:
                raise AssertionError(
                    f"{label} did not preserve its verified band route"
                )
            if "[alarm]" in strict.stderr:
                raise AssertionError(f"{label} raised an alarm for an optional annotation")
            if VECTOR_HINT_SKIPPED not in strict.stderr:
                raise AssertionError(
                    f"{label} omitted its explicit vector-skip telemetry"
                )
            if "vector for" in strict.stdout:
                raise AssertionError(f"{label} adopted a rejected vector consumer")
            expected_markers = ("/ 256", "8 *", "32 *") if second_level else ("/ 32", "32 *")
            for marker in expected_markers:
                if marker not in strict.stdout:
                    raise AssertionError(
                        f"{label} lost verified tiling marker {marker!r}"
                    )

    consumer_failure_count = check_consumer_failure_cases(
        polopt=polopt,
        root=root,
        timeout=timeout,
    )
    malformed_consumer_count = check_malformed_tiling_with_explicit_consumers(
        polopt=polopt,
        wrapper=wrapper,
        real_pluto=real_pluto,
        root=root,
        timeout=timeout,
    )
    malformed_hinted_consumer_count = (
        check_malformed_tiling_with_hinted_consumers(
            polopt=polopt,
            wrapper=wrapper,
            real_pluto=real_pluto,
            root=root,
            timeout=timeout,
        )
    )
    final_affine_count = check_final_affine_failure_cases(
        polopt=polopt,
        wrapper=wrapper,
        real_pluto=real_pluto,
        root=root,
        timeout=timeout,
    )

    print(
        "[second-level-rejection] PASS "
        "expected=malformed:16,scalar-only:1,nonpermutable:1,vector-skips:4,"
        "consumer-failures:12,malformed-explicit:16,malformed-hinted:18,"
        "final-affine:48 "
        f"actual=malformed:{malformed_count},scalar-only:1,nonpermutable:1,"
        f"vector-skips:4,consumer-failures:{consumer_failure_count},"
        f"malformed-explicit:{malformed_consumer_count},"
        f"malformed-hinted:{malformed_hinted_consumer_count},"
        f"final-affine:{final_affine_count} "
        "interpretation=producer-consumer-and-final-affine-failures-preserved-the-declared-route",
        flush=True,
    )


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[2]
    check_rejected_tiling_route(
        polopt=(root / "polopt").resolve(),
        fixture=(
            root
            / "tools"
            / "second_level_tiling"
            / "fixtures"
            / "symbolic-independent-2d.loop"
        ),
        timeout=180,
    )
