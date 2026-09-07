#!/usr/bin/env python3
from __future__ import annotations

import subprocess
import sys
import os
import re
import tempfile
from dataclasses import dataclass
from pathlib import Path

import pluto_compat_driver as compat


ROOT = Path(__file__).resolve().parents[2]
POLOPT = ROOT / "polopt"


@dataclass(frozen=True)
class Check:
    name: str
    args: list[str]
    fixture: Path
    success: bool
    needle: str
    normalized: str | None = None
    effect_needles: tuple[str, ...] = ()
    effect_absent: tuple[str, ...] = ()
    scheduled_needles: tuple[str, ...] = ()
    scheduled_absent: tuple[str, ...] = ()
    stderr_needles: tuple[str, ...] = ()
    stderr_absent: tuple[str, ...] = ()
    tiling_route: str | None = None
    differs_from_args: tuple[tuple[str, ...], ...] = ()
    implicit_control_file: str | None = None
    implicit_control_file_content: str = "16\n"
    explicit_control_flag: str | None = None
    explicit_control_file_content: str = "16\n"
    env: dict[str, str] | None = None
    same_as_args: tuple[str, ...] | None = None
    native: bool = False
    second_level_markers: tuple[str, ...] | None = None
    effect_patterns: tuple[str, ...] = ()


FLAGS = ["--tile", "--smartfuse", "--nointratileopt", "--noprevector", "--nounrolljam", "--rar"]
FLAGS_PREVECTOR = ["--tile", "--smartfuse", "--nointratileopt", "--prevector", "--nounrolljam", "--rar"]
FLAGS_INTRATILE = ["--tile", "--smartfuse", "--intratileopt", "--noprevector", "--nounrolljam", "--rar"]
DEFAULT_NO_RAR_FLAGS = ["--tile", "--smartfuse", "--nointratileopt", "--noprevector", "--nounrolljam"]
DEFAULT_NO_RAR_NOTILE = ["--notile", "--smartfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel"]
DEFAULT_NO_RAR_IDENTITY_NOTILE = ["--identity", "--notile", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel"]
MATMUL_NOTILE = ["--notile", "--smartfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
MATMUL_TILED = [*FLAGS, "--nodiamond-tile", "--noparallel"]
MATMUL_TILED_PREVECTOR = [*FLAGS_PREVECTOR, "--nodiamond-tile", "--noparallel"]
MATMUL_TILED_DEFAULT_PREVECTOR = ["--tile", "--smartfuse", "--nointratileopt", "--nounrolljam", "--rar", "--nodiamond-tile", "--noparallel"]
MATMUL_TILED_INTRATILE = [*FLAGS_INTRATILE, "--nodiamond-tile", "--noparallel"]
MATMUL_TILED_DETERMINE = [*FLAGS, "--determine-tile-size", "--nodiamond-tile", "--noparallel"]
MATMUL_TILED_DETERMINE_CACHE = [*FLAGS, "--determine-tile-size", "--cache-size=32768", "--nodiamond-tile", "--noparallel"]
MATMUL_TILED_DETERMINE_DATA = [*FLAGS, "--determine-tile-size", "--data-element-size=16", "--nodiamond-tile", "--noparallel"]
MATMUL_TILED_DETERMINE_UFACTOR = [*FLAGS, "--determine-tile-size", "--cache-size=32768", "--data-element-size=8", "--ufactor=3", "--nodiamond-tile", "--noparallel"]
CONST_UNROLL_UFACTOR = ["--notile", "--nointratileopt", "--noprevector", "--unrolljam", "--ufactor=3", "--nodiamond-tile", "--noparallel", "--rar"]
IDENTITY_TILED = ["--identity", "--tile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel", "--rar"]
IDENTITY_TILED_SECOND_LEVEL = ["--identity", "--tile", "--second-level-tile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel", "--rar"]
IDENTITY_TILED_SECOND_LEVEL_ISS = ["--identity", "--tile", "--iss", "--second-level-tile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel", "--rar"]
IDENTITY_TILED_PARALLEL = ["--identity", "--tile", "--parallel", "--innerpar", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--rar"]
IDENTITY_TILED_MULTIPAR = ["--identity", "--tile", "--parallel", "--multipar", "--innerpar", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--rar"]
FUSION_NOTILE_SMART = ["--notile", "--smartfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
FUSION_NOTILE_NOFUSE = ["--notile", "--nofuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
FUSION_NOTILE_MAXFUSE = ["--notile", "--maxfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
FUSION_NOTILE_NODEPBOUND = ["--notile", "--smartfuse", "--nodepbound", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_PER_CC = ["--notile", "--smartfuse", "--per-cc-obj", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_FLIC = ["--notile", "--smartfuse", "--flic", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_FAST_LIN = ["--notile", "--smartfuse", "--fast-lin-ind-check", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_LASTWRITER = ["--notile", "--smartfuse", "--lastwriter", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_NOLASTWRITER = ["--notile", "--smartfuse", "--nolastwriter", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_CANDLDEP = ["--notile", "--smartfuse", "--candldep", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_CANDLDEP_SCALPRIV = ["--notile", "--smartfuse", "--candldep", "--scalpriv", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_CANDLDEP_SCALPRIV_PARALLEL = ["--notile", "--smartfuse", "--candldep", "--scalpriv", "--parallel", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--rar"]
TUNING_NOTILE_PIPSOLVE = ["--notile", "--smartfuse", "--pipsolve", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_ISL_ACCESSWISE = ["--notile", "--smartfuse", "--isldepaccesswise", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_ISL_STMTWISE = ["--notile", "--smartfuse", "--isldepstmtwise", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_ISL_COALESCE = ["--notile", "--smartfuse", "--isldepcoalesce", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_COEFF_BOUND = ["--notile", "--smartfuse", "--coeff-bound=10", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_COEFF_BOUND_TIGHT = ["--notile", "--smartfuse", "--coeff-bound=1", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_FORCEPARALLEL = ["--notile", "--smartfuse", "--forceparallel=1", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_GLPK = ["--notile", "--smartfuse", "--glpk", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_ILP = ["--notile", "--smartfuse", "--glpk", "--ilp", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_LP = ["--notile", "--smartfuse", "--glpk", "--lp", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_LPCOLOR = ["--notile", "--smartfuse", "--glpk", "--lpcolor", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_DFP = ["--notile", "--smartfuse", "--glpk", "--dfp", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_CLUSTERSCC = ["--notile", "--smartfuse", "--glpk", "--clusterscc", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_HYBRIDFUSE = ["--notile", "--smartfuse", "--glpk", "--hybridfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_DELAYEDCUT = ["--notile", "--smartfuse", "--glpk", "--dfp", "--delayedcut", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_TYPEDFUSE = ["--notile", "--typedfuse", "--glpk", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
MATMUL_TILED_PARTIAL_LEVELS = [*FLAGS, "--ft=0", "--lt=1", "--nodiamond-tile", "--noparallel"]
JACOBI_NODIAMOND = [*FLAGS, "--nodiamond-tile", "--noparallel"]
JACOBI_NODIAMOND_ISS = [*FLAGS, "--nodiamond-tile", "--noparallel", "--iss"]
JACOBI_DIAMOND = [*FLAGS, "--diamond-tile", "--noparallel"]
JACOBI_DIAMOND_ISS = [*FLAGS, "--diamond-tile", "--noparallel", "--iss"]
JACOBI_FULL_DIAMOND = [*FLAGS, "--full-diamond-tile", "--noparallel"]
JACOBI_FULL_DIAMOND_ISS = [*FLAGS, "--full-diamond-tile", "--noparallel", "--iss"]
MATMUL = ROOT / "tests" / "polopt-generated" / "inputs" / "matmul.loop"
REG_MATMUL = ROOT / "tests" / "polopt-regression" / "inputs" / "matmul.loop"
FUSION1 = ROOT / "tests" / "polopt-regression" / "inputs" / "fusion1.loop"
FUSION2 = ROOT / "tests" / "polopt-regression" / "inputs" / "fusion2.loop"
FUSION6 = ROOT / "tests" / "polopt-regression" / "inputs" / "fusion6.loop"
FUSION7 = ROOT / "tests" / "polopt-regression" / "inputs" / "fusion7.loop"
FUSION10 = ROOT / "tests" / "polopt-regression" / "inputs" / "fusion10.loop"
SCALPRIV = ROOT / "tests" / "polopt-regression" / "inputs" / "scalpriv.loop"
CONST_UNROLL = ROOT / "tests" / "polopt-regression" / "inputs" / "const_unroll.loop"
MIXED_UNROLL = ROOT / "tests" / "polopt-regression" / "inputs" / "mixed_unroll.loop"
UNROLLJAM_CONTEXT_BOUND_ESCAPE = ROOT / "tests" / "polopt-regression" / "inputs" / "unrolljam_context_bound_escape.loop"
STRIDE_EVEN = ROOT / "tests" / "polopt-regression" / "inputs" / "stride_even.loop"
STRIDE_DOWN = ROOT / "tests" / "polopt-regression" / "inputs" / "stride_down.loop"
STRIDE_BAD_ZERO = ROOT / "tests" / "polopt-regression" / "inputs" / "stride_bad_zero.loop"
STRIDE_BAD_SYMBOLIC = ROOT / "tests" / "polopt-regression" / "inputs" / "stride_bad_symbolic.loop"
PCA = ROOT / "tests" / "polopt-regression" / "inputs" / "pca.loop"
COSTFUNC = ROOT / "tests" / "polopt-regression" / "inputs" / "costfunc.loop"
ADI = ROOT / "tests" / "polopt-regression" / "inputs" / "adi.loop"
CORCOL = ROOT / "tests" / "polopt-regression" / "inputs" / "corcol.loop"
JACOBI_1D = ROOT / "tests" / "polopt-generated" / "inputs" / "jacobi-1d-imper.loop"
NODEP = ROOT / "tests" / "polopt-regression" / "inputs" / "nodep.loop"
TRIPLE_NODEP = ROOT / "tests" / "polopt-regression" / "inputs" / "triple-nodep.loop"
MATMUL_INIT = ROOT / "tools" / "second_level_tiling" / "fixtures" / "matmul-init.loop"
SYMBOLIC_SECOND_LEVEL = ROOT / "tools" / "second_level_tiling" / "fixtures" / "symbolic-independent-2d.loop"
DIAMOND_PARALLEL_BATCH = ROOT / "tools" / "parallel_current" / "fixtures" / "diamond-example-inner-batch.loop"
JACOBI_BATCH = ROOT / "tools" / "parallel_current" / "fixtures" / "jacobi-batch.loop"


CHECKS = [
    # The original compatibility corpus was calibrated with RAR enabled, either
    # explicitly here or implicitly by the old Scheduler recipes.  These cases
    # independently calibrate the user-facing policy in which omitting --rar
    # follows Pluto's default.  Do not obtain them by mutating the RAR corpus:
    # the two policies may legitimately select different schedules.
    Check(
        "default-no-rar-affine",
        DEFAULT_NO_RAR_NOTILE,
        FUSION2,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse",
        effect_needles=("for i0 in range",),
        stderr_absent=("[alarm]",),
        differs_from_args=(tuple(DEFAULT_NO_RAR_IDENTITY_NOTILE),),
    ),
    Check(
        "default-no-rar-tiled",
        [*DEFAULT_NO_RAR_FLAGS, "--nodiamond-tile", "--noparallel"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse",
        effect_needles=("32 *", "/ 32"),
        stderr_absent=("[alarm]",),
        tiling_route="permutable-band",
    ),
    Check(
        "default-no-rar-tiled-iss",
        [*DEFAULT_NO_RAR_FLAGS, "--nodiamond-tile", "--noparallel", "--iss"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss",
        effect_needles=("32 *", "/ 32"),
        stderr_absent=("[alarm]",),
        tiling_route="permutable-band",
    ),
    Check(
        "default-no-rar-parallel",
        [*DEFAULT_NO_RAR_FLAGS, "--nodiamond-tile", "--parallel", "--innerpar"],
        NODEP,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse",
        effect_needles=("parallel for", "32 *"),
        stderr_absent=("[alarm]",),
        tiling_route="permutable-band",
    ),
    Check(
        "default-no-rar-vector",
        ["--tile", "--smartfuse", "--nointratileopt", "--prevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"],
        SYMBOLIC_SECOND_LEVEL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse",
        effect_needles=("vector for i3", "32 *", "/ 32"),
        stderr_needles=("[vector-validation] status=applied",),
        stderr_absent=("[alarm]",),
        tiling_route="permutable-band",
    ),
    Check(
        "default-no-rar-vector-matmul-no-hint",
        ["--tile", "--smartfuse", "--nointratileopt", "--prevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse",
        effect_needles=("32 *", "/ 32"),
        effect_absent=("vector for",),
        stderr_needles=("[vector-validation] status=skipped reason=no-hint",),
        stderr_absent=("[alarm]",),
        tiling_route="permutable-band",
    ),
    Check(
        "default-no-rar-diamond",
        [*DEFAULT_NO_RAR_FLAGS, "--diamond-tile", "--noparallel"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse",
        effect_needles=("32 *", "i4 + (-1 * i5)"),
        stderr_absent=("[alarm]",),
        tiling_route="permutable-band",
    ),
    Check(
        "default-no-rar-second-level",
        [*DEFAULT_NO_RAR_FLAGS, "--nodiamond-tile", "--noparallel", "--second-level-tile"],
        SYMBOLIC_SECOND_LEVEL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse",
        effect_needles=("/ 256", "8 *", "32 *"),
        stderr_absent=("[alarm]",),
        tiling_route="permutable-band",
    ),
    Check(
        "default-no-rar-islsolve-default",
        [*DEFAULT_NO_RAR_NOTILE, "--islsolve"],
        FUSION2,
        True,
        "== Optimized Loop ==",
        "--islsolve accepted as Pluto's default scheduler solver",
        effect_needles=("for i0 in range",),
        stderr_absent=("[alarm]",),
        same_as_args=tuple(DEFAULT_NO_RAR_NOTILE),
    ),
    Check(
        "default-no-rar-diagnostic-noops",
        [*DEFAULT_NO_RAR_NOTILE, "--debug", "--moredebug", "--silent"],
        FUSION2,
        True,
        "== Optimized Loop ==",
        "--debug accepted as a logging-only no-op",
        effect_needles=("for i0 in range",),
        stderr_absent=("[alarm]",),
        same_as_args=tuple(DEFAULT_NO_RAR_NOTILE),
    ),
    Check(
        "default-no-rar-codegen-noop",
        [*DEFAULT_NO_RAR_NOTILE, "--nocloogbacktrack"],
        FUSION2,
        True,
        "== Optimized Loop ==",
        "--nocloogbacktrack accepted as a no-op because PolOpt does not use Pluto's CLooG code generator",
        effect_needles=("for i0 in range",),
        stderr_absent=("[alarm]",),
        same_as_args=tuple(DEFAULT_NO_RAR_NOTILE),
    ),
    Check(
        "ordinary-tiled",
        MATMUL_TILED,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: <default>",
        effect_needles=("32 *", "/ 32"),
        differs_from_args=(tuple(MATMUL_NOTILE),),
    ),
    Check(
        "ordinary-tiled-iss",
        [*FLAGS, "--nodiamond-tile", "--noparallel", "--iss"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss",
        effect_needles=("32 *", "/ 32"),
    ),
    Check(
        "ordinary-legacy-alias-band",
        [*MATMUL_TILED, "--legacy-generic-tiling"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: <default>",
        effect_needles=("32 *", "/ 32"),
        differs_from_args=(tuple(MATMUL_NOTILE),),
    ),
    Check(
        "ordinary-band-experiment-alias",
        [*MATMUL_TILED, "--band-tiling-experiment"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        effect_needles=("32 *", "/ 32"),
        differs_from_args=(tuple(MATMUL_NOTILE),),
    ),
    Check(
        "optimizer-intratileopt",
        MATMUL_TILED_INTRATILE,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --intratileopt",
        effect_needles=("for i0 in range(0, ((K + 31) / 32))",),
        differs_from_args=(tuple(MATMUL_TILED),),
    ),
    Check(
        "intratileopt-iss",
        [*MATMUL_TILED_INTRATILE, "--iss"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss",
        effect_needles=("32 *", "/ 32"),
    ),
    Check(
        "intratileopt-second-level",
        [*MATMUL_TILED_INTRATILE, "--second-level-tile"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --second-level-tile",
        tiling_route="permutable-band",
        second_level_markers=("(i0 / 8)", "32 *"),
    ),
    Check(
        "intratileopt-second-level-iss",
        [*MATMUL_TILED_INTRATILE, "--second-level-tile", "--iss"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --second-level-tile",
        tiling_route="permutable-band",
        second_level_markers=("(i0 / 8)", "32 *"),
    ),
    Check(
        "intratileopt-identity-tiled",
        ["--identity", "--tile", "--intratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel", "--rar"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --identity --tile",
        effect_needles=("32 *", "/ 32"),
    ),
    Check(
        "intratileopt-identity-tiled-iss",
        ["--identity", "--tile", "--intratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel", "--rar", "--iss"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --identity --tile",
        effect_needles=("32 *", "/ 32"),
    ),
    Check(
        "intratileopt-parallel",
        [*FLAGS_INTRATILE, "--nodiamond-tile", "--parallel", "--innerpar"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --parallel",
        effect_needles=("parallel for", "32 *"),
    ),
    Check(
        "intratileopt-parallel-iss",
        [*FLAGS_INTRATILE, "--nodiamond-tile", "--parallel", "--innerpar", "--iss"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --parallel",
        effect_needles=("parallel for", "32 *"),
        tiling_route="permutable-band",
    ),
    Check(
        "intratileopt-vector",
        ["--tile", "--smartfuse", "--intratileopt", "--prevector", "--nounrolljam", "--rar", "--nodiamond-tile", "--noparallel"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --vector",
        effect_needles=("vector for", "32 *"),
        stderr_needles=("[vector-validation] status=applied",),
    ),
    Check(
        "intratileopt-diamond",
        [*FLAGS_INTRATILE, "--diamond-tile", "--noparallel"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --diamond-tile",
        effect_needles=("32 *",),
    ),
    Check(
        "intratileopt-diamond-iss",
        [*FLAGS_INTRATILE, "--diamond-tile", "--noparallel", "--iss"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --diamond-tile",
        effect_needles=("32 *",),
    ),
    Check(
        "native-intratileopt",
        ["--intratileopt"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        effect_needles=("32 *", "/ 32"),
        native=True,
    ),
    Check(
        "native-dump-affine-only",
        ["--notile", "--dump-scheduled-openscop"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        scheduled_needles=("1 9 1 3 0 3",),
        scheduled_absent=("1 12 1 6 0 3",),
        effect_absent=("32 *", "/ 32"),
        native=True,
    ),
    Check(
        "native-dump-intratileopt",
        ["--intratileopt", "--dump-scheduled-openscop"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        scheduled_needles=("1 12 1 6 0 3",),
        scheduled_absent=("1 9 1 3 0 3",),
        effect_needles=("32 *", "/ 32"),
        native=True,
    ),
    Check(
        "native-dump-identity-intratileopt",
        ["--identity-tiled", "--intratileopt", "--dump-scheduled-openscop"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        scheduled_needles=("1 12 1 6 0 3",),
        effect_needles=("32 *", "/ 32"),
        native=True,
    ),
    Check(
        "native-dump-iss-intratileopt",
        ["--iss", "--intratileopt", "--dump-scheduled-openscop"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        scheduled_needles=("1 12 1 6 0 3",),
        effect_needles=("32 *", "/ 32"),
        native=True,
    ),
    Check(
        "native-dump-parallel-intratileopt",
        ["--parallel", "--intratileopt", "--dump-scheduled-openscop"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        scheduled_needles=("1 12 1 6 0 3",),
        effect_needles=("parallel for", "32 *"),
        native=True,
    ),
    Check(
        "native-dump-vector-intratileopt",
        ["--vector", "--intratileopt", "--dump-scheduled-openscop"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        scheduled_needles=("1 12 1 6 0 3",),
        effect_needles=("vector for", "32 *"),
        stderr_needles=("[vector-validation] status=applied",),
        native=True,
    ),
    Check(
        "native-reject-tile-notile-forward",
        ["--identity-tiled", "--notile"],
        MATMUL,
        False,
        "--tile and --notile select contradictory tiling routes",
        native=True,
    ),
    Check(
        "native-reject-tile-notile-reverse",
        ["--notile", "--identity-tiled"],
        MATMUL,
        False,
        "--tile and --notile select contradictory tiling routes",
        native=True,
    ),
    Check(
        "native-reject-intratile-notile-forward",
        ["--intratileopt", "--notile"],
        MATMUL,
        False,
        "--intratileopt requires a tiling route",
        native=True,
    ),
    Check(
        "native-reject-intratile-notile-reverse",
        ["--notile", "--intratileopt"],
        MATMUL,
        False,
        "--intratileopt requires a tiling route",
        native=True,
    ),
    Check(
        "native-reject-intratile-identity-without-tile",
        ["--identity", "--intratileopt"],
        MATMUL,
        False,
        "--intratileopt requires a tiling route",
        native=True,
    ),
    Check(
        "native-reject-intratile-policy-forward",
        ["--intratileopt", "--nointratileopt"],
        MATMUL,
        False,
        "contradictory intra-tile policies",
        native=True,
    ),
    Check(
        "native-reject-intratile-policy-reverse",
        ["--nointratileopt", "--intratileopt"],
        MATMUL,
        False,
        "contradictory intra-tile policies",
        native=True,
    ),
    Check(
        "native-const-unroll-constant-range",
        ["--identity", "--const-unroll"],
        CONST_UNROLL,
        True,
        "a[3] = 3;",
        effect_absent=("for i0 in range",),
        native=True,
    ),
    Check(
        "native-const-unroll-inside-parallel-current",
        ["--identity", "--const-unroll", "--parallel-current", "0"],
        NODEP,
        True,
        "parallel for i0",
        effect_needles=("A[((4 * i0) + 3)]",),
        effect_absent=("for i1 in range",),
        native=True,
    ),
    Check(
        "native-const-unroll-inside-parallel-hint",
        ["--notile", "--parallel", "--const-unroll"],
        NODEP,
        True,
        "parallel for i0",
        effect_needles=("A[((4 * i0) + 3)]",),
        effect_absent=("for i1 in range",),
        native=True,
    ),
    Check(
        "native-const-unroll-preserves-parallel-loop",
        ["--identity", "--const-unroll", "--parallel-current", "0"],
        CONST_UNROLL,
        False,
        "constant unroll requested, but no constant-bound sequential loop exists",
        native=True,
    ),
    Check(
        "native-reject-const-unroll-vector-current",
        ["--identity", "--const-unroll", "--vector-current", "0"],
        MATMUL,
        False,
        "--const-unroll cannot currently be combined with vector execution",
        native=True,
    ),
    Check(
        "optimizer-determine-tile-size",
        MATMUL_TILED_DETERMINE,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --determine-tile-size",
        effect_needles=("2048 *",),
        differs_from_args=(tuple(MATMUL_TILED),),
    ),
    Check(
        "optimizer-cache-size",
        MATMUL_TILED_DETERMINE_CACHE,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --determine-tile-size --cache-size=32768",
        effect_needles=("64 *",),
        differs_from_args=(tuple(MATMUL_TILED_DETERMINE),),
    ),
    Check(
        "optimizer-data-element-size",
        MATMUL_TILED_DETERMINE_DATA,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --determine-tile-size --data-element-size=16",
        effect_needles=("1024 *",),
        differs_from_args=(tuple(MATMUL_TILED_DETERMINE),),
    ),
    Check(
        "optimizer-ufactor-tile-model",
        MATMUL_TILED_DETERMINE_UFACTOR,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --determine-tile-size --cache-size=32768 --data-element-size=8 --ufactor=3",
        effect_needles=("63 *",),
        differs_from_args=(tuple(MATMUL_TILED_DETERMINE_CACHE),),
    ),
    Check(
        "affine-only",
        MATMUL_NOTILE,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --notile",
        effect_absent=("32 *", "/ 32"),
    ),
    Check(
        "optimizer-nofuse-affine",
        FUSION_NOTILE_NOFUSE,
        FUSION1,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --nofuse",
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-maxfuse-affine",
        FUSION_NOTILE_MAXFUSE,
        FUSION6,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --maxfuse",
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-nodepbound-affine",
        FUSION_NOTILE_NODEPBOUND,
        FUSION2,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --nodepbound",
        effect_needles=("for i2 in range((i0 + -1), i0)", "B[i2][i3]"),
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-per-cc-obj-affine",
        TUNING_NOTILE_PER_CC,
        PCA,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --per-cc-obj",
        effect_needles=("for i1 in range((i0 + 1), (m + 1))", "mean[m] = 0.0;"),
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-flic-affine",
        TUNING_NOTILE_FLIC,
        COSTFUNC,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --flic",
        effect_needles=("for i1 in range(1, N)", "a[i0][i1] ="),
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-fast-lin-ind-check-affine",
        TUNING_NOTILE_FAST_LIN,
        COSTFUNC,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --fast-lin-ind-check",
        effect_needles=("for i1 in range(1, N)", "a[i0][i1] ="),
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-lastwriter-affine",
        TUNING_NOTILE_LASTWRITER,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --lastwriter",
        effect_needles=("for i0 in range(0, M)",),
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-nolastwriter-affine",
        TUNING_NOTILE_NOLASTWRITER,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --nolastwriter",
    ),
    Check(
        "optimizer-pipsolve-affine",
        TUNING_NOTILE_PIPSOLVE,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --pipsolve",
    ),
    Check(
        "optimizer-isldepaccesswise-affine",
        TUNING_NOTILE_ISL_ACCESSWISE,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --isldepaccesswise",
    ),
    Check(
        "optimizer-isldepstmtwise-affine",
        TUNING_NOTILE_ISL_STMTWISE,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --isldepstmtwise",
    ),
    Check(
        "optimizer-isldepcoalesce-affine",
        TUNING_NOTILE_ISL_COALESCE,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --isldepcoalesce",
    ),
    Check(
        "optimizer-coeff-bound-affine",
        TUNING_NOTILE_COEFF_BOUND,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --coeff-bound=10",
    ),
    Check(
        "optimizer-coeff-bound-tight-effect",
        TUNING_NOTILE_COEFF_BOUND_TIGHT,
        FUSION10,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --coeff-bound=1",
        effect_needles=("A[(2 * i0)] = 1;", "B[3] = A[3];"),
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-forceparallel-pass-through",
        TUNING_NOTILE_FORCEPARALLEL,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --forceparallel=1",
    ),
    Check("identity-notile", ["--identity", "--notile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel", "--rar"], MATMUL, True, "== Optimized Loop ==", "polopt args: --identity"),
    Check(
        "reject-sequential-iss-identity",
        ["--identity", "--notile", "--iss", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"],
        MATMUL,
        False,
        "sequential --iss --identity is not a verified compiler route",
    ),
    Check(
        "sequential-iss-notile",
        [*MATMUL_NOTILE, "--iss"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --notile",
        stderr_absent=("[tiling-validation]",),
    ),
    Check(
        "partial-tiling-levels",
        MATMUL_TILED_PARTIAL_LEVELS,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --ft=0 --lt=1",
        effect_needles=("32 *", "/ 32"),
    ),
    Check(
        "second-level",
        [*FLAGS, "--nodiamond-tile", "--noparallel", "--second-level-tile"],
        MATMUL_INIT,
        True,
        "== Optimized Loop ==",
        "polopt args: --second-level-tile",
        tiling_route="permutable-band",
        differs_from_args=(tuple(MATMUL_TILED),),
    ),
    Check(
        "second-level-iss",
        [*FLAGS, "--nodiamond-tile", "--noparallel", "--iss", "--second-level-tile"],
        MATMUL_INIT,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --second-level-tile",
        effect_needles=("8 *", "/ 256", "32 *"),
        tiling_route="permutable-band",
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--noparallel", "--iss"]),),
    ),
    Check(
        "parallel",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--innerpar"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --parallel",
        effect_needles=("parallel for",),
        differs_from_args=(tuple(MATMUL_TILED),),
    ),
    Check(
        "parallel-strict-hint-only",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--parallel-strict", "--innerpar"],
        SYMBOLIC_SECOND_LEVEL,
        True,
        "== Optimized Loop ==",
        "polopt args: --parallel --parallel-strict",
        effect_needles=("parallel for", "32 *", "/ 32"),
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--noparallel"]),),
    ),
    Check(
        "parallel-multipar",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--multipar", "--innerpar"],
        NODEP,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --multipar",
        effect_needles=("parallel for i0", "parallel for i2"),
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--parallel", "--innerpar"]),),
    ),
    Check(
        "parallel-multipar-strict-hint-only",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--multipar", "--parallel-strict", "--innerpar"],
        NODEP,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --multipar",
        effect_needles=("parallel for i0",),
        effect_absent=("parallel for i2",),
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--parallel", "--multipar", "--innerpar"]),),
    ),
    Check(
        "parallel-multipar-three-dims",
        ["--notile", "--smartfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--rar", "--parallel", "--multipar", "--innerpar"],
        TRIPLE_NODEP,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --multipar",
        effect_needles=("parallel for i0", "parallel for i1", "parallel for i2"),
        differs_from_args=(tuple(["--notile", "--smartfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--rar", "--parallel", "--innerpar"]),),
    ),
    Check(
        "second-level-parallel",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--innerpar", "--second-level-tile"],
        SYMBOLIC_SECOND_LEVEL,
        True,
        "== Optimized Loop ==",
        "polopt args: --second-level-tile --parallel",
        effect_needles=("parallel for", "/ 256", "8 *", "32 *"),
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--noparallel", "--second-level-tile"]),),
    ),
    Check(
        "second-level-parallel-matmul-init",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--innerpar", "--second-level-tile"],
        MATMUL_INIT,
        True,
        "== Optimized Loop ==",
        "polopt args: --second-level-tile --parallel",
        effect_needles=("parallel for i0", "/ 256", "8 *", "32 *"),
        tiling_route="permutable-band",
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--noparallel", "--second-level-tile"]),),
    ),
    Check(
        "second-level-parallel-multipar",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--multipar", "--innerpar", "--second-level-tile"],
        SYMBOLIC_SECOND_LEVEL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --multipar",
        effect_needles=("parallel for i0", "parallel for i1", "/ 256", "8 *", "32 *"),
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--parallel", "--innerpar", "--second-level-tile"]),),
    ),
    Check(
        "second-level-parallel-iss",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--innerpar", "--second-level-tile", "--iss"],
        SYMBOLIC_SECOND_LEVEL,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --second-level-tile --parallel",
        effect_needles=("parallel for", "/ 256", "8 *", "32 *"),
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--noparallel", "--second-level-tile", "--iss"]),),
    ),
    Check(
        "second-level-parallel-multipar-iss",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--multipar", "--innerpar", "--second-level-tile", "--iss"],
        SYMBOLIC_SECOND_LEVEL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --multipar",
        effect_needles=("parallel for i0", "parallel for i1", "/ 256", "8 *", "32 *"),
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--parallel", "--innerpar", "--second-level-tile", "--iss"]),),
    ),
    Check(
        "diamond",
        JACOBI_DIAMOND,
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --diamond-tile",
        effect_needles=("32 *",),
    ),
    Check(
        "diamond-iss",
        JACOBI_DIAMOND_ISS,
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --diamond-tile",
        effect_needles=("32 *",),
    ),
    Check(
        "diamond-parallel",
        [*FLAGS, "--diamond-tile", "--parallel"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --diamond-tile --parallel",
        effect_needles=("parallel for", "32 *", "/ 32", "i4 + (-1 * i5)"),
        differs_from_args=(tuple(JACOBI_DIAMOND),),
    ),
    Check(
        "diamond-parallel-innerpar",
        [*FLAGS, "--diamond-tile", "--parallel", "--innerpar"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --innerpar",
        effect_needles=("parallel for", "32 *", "i4 + (-1 * i5)"),
        stderr_absent=("[alarm]",),
    ),
    Check(
        "diamond-parallel-strict-hint-only",
        [*FLAGS, "--diamond-tile", "--parallel", "--parallel-strict"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --diamond-tile --parallel --parallel-strict",
        effect_needles=("parallel for", "32 *", "i4 + (-1 * i5)"),
        differs_from_args=(tuple([*FLAGS, "--diamond-tile", "--noparallel"]),),
    ),
    Check(
        "diamond-parallel-multipar",
        [*FLAGS, "--diamond-tile", "--parallel", "--multipar", "--innerpar"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --multipar",
        effect_needles=("parallel for i0", "parallel for i5", "i4 + (-1 * i5)"),
        differs_from_args=(tuple([*FLAGS, "--diamond-tile", "--parallel", "--innerpar"]),),
    ),
    Check(
        "diamond-parallel-multipar-strict-hint-only",
        [*FLAGS, "--diamond-tile", "--parallel", "--multipar", "--parallel-strict", "--innerpar"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --multipar",
        effect_needles=("parallel for i0", "i4 + (-1 * i5)"),
        effect_absent=("parallel for i5",),
        differs_from_args=(tuple([*FLAGS, "--diamond-tile", "--parallel", "--multipar", "--innerpar"]),),
    ),
    Check(
        "diamond-iss-parallel",
        [*FLAGS, "--diamond-tile", "--parallel", "--iss"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --diamond-tile --parallel",
        effect_needles=("parallel for", "32 *", "/ 32", "i4 + (-1 * i5)"),
        differs_from_args=(tuple(JACOBI_DIAMOND_ISS),),
    ),
    Check(
        "diamond-vector",
        ["--tile", "--smartfuse", "--nointratileopt", "--nounrolljam", "--rar", "--diamond-tile", "--noparallel", "--vector"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --diamond-tile --vector",
        effect_needles=("32 *", "i4 + (-1 * i5)"),
        effect_absent=("vector for",),
        stderr_needles=(
            "[vector-validation] status=skipped reason=hint-not-certifiable-or-non-innermost",
        ),
        stderr_absent=("[alarm]",),
        same_as_args=tuple([*FLAGS, "--diamond-tile", "--noparallel"]),
    ),
    Check(
        "diamond-vector-strict-hint-only",
        ["--tile", "--smartfuse", "--nointratileopt", "--nounrolljam", "--rar", "--diamond-tile", "--noparallel", "--vector", "--vector-strict"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --diamond-tile --vector --vector-strict",
        effect_needles=("32 *", "i4 + (-1 * i5)"),
        effect_absent=("vector for",),
        stderr_needles=(
            "[vector-validation] status=skipped reason=hint-not-certifiable-or-non-innermost",
        ),
        stderr_absent=("[alarm]",),
        same_as_args=tuple([*FLAGS, "--diamond-tile", "--noparallel"]),
    ),
    Check(
        "diamond-iss-parallel-multipar",
        [*FLAGS, "--diamond-tile", "--parallel", "--multipar", "--innerpar", "--iss"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --rar --multipar",
        effect_needles=("parallel for i0", "parallel for i5", "i4 + (-1 * i5)"),
        differs_from_args=(tuple([*FLAGS, "--diamond-tile", "--parallel", "--iss"]),),
    ),
    Check(
        "diamond-parallel-jacobi-batch",
        [*FLAGS, "--diamond-tile", "--parallel"],
        JACOBI_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --diamond-tile --parallel",
        effect_needles=("parallel for", "64 *", "(-2 * i11)", "a[", "b["),
        differs_from_args=(tuple(JACOBI_DIAMOND),),
    ),
    Check(
        "diamond-second-level",
        [*FLAGS, "--diamond-tile", "--noparallel", "--second-level-tile"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --second-level-tile --diamond-tile",
        effect_needles=("32 *",),
        tiling_route="permutable-band",
        differs_from_args=(tuple(JACOBI_NODIAMOND), tuple(JACOBI_DIAMOND)),
    ),
    Check(
        "diamond-iss-second-level",
        [*FLAGS, "--diamond-tile", "--noparallel", "--iss", "--second-level-tile"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --second-level-tile --diamond-tile",
        effect_needles=("32 *",),
        tiling_route="permutable-band",
        differs_from_args=(tuple(JACOBI_NODIAMOND_ISS), tuple(JACOBI_DIAMOND_ISS)),
    ),
    Check(
        "full-diamond",
        JACOBI_FULL_DIAMOND,
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --full-diamond-tile",
        effect_needles=("32 *",),
    ),
    Check(
        "full-diamond-batch",
        [*FLAGS, "--full-diamond-tile", "--noparallel"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --full-diamond-tile",
        effect_needles=("32 *", "i4 + (-1 * i5)"),
    ),
    Check(
        "full-diamond-iss",
        JACOBI_FULL_DIAMOND_ISS,
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --full-diamond-tile",
        effect_needles=("32 *",),
    ),
    Check(
        "full-diamond-parallel",
        [*FLAGS, "--full-diamond-tile", "--parallel"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        effect_needles=("parallel for", "32 *", "i4 + (-1 * i5)"),
        differs_from_args=(tuple(JACOBI_FULL_DIAMOND),),
    ),
    Check(
        "full-diamond-parallel-iss",
        [*FLAGS, "--full-diamond-tile", "--parallel", "--iss"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        effect_needles=("parallel for", "32 *", "i4 + (-1 * i5)"),
        differs_from_args=(tuple(JACOBI_FULL_DIAMOND_ISS),),
    ),
    Check(
        "full-diamond-vector",
        ["--tile", "--smartfuse", "--nointratileopt", "--nounrolljam", "--rar", "--full-diamond-tile", "--noparallel", "--vector"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        effect_needles=("32 *", "i4 + (-1 * i5)"),
        effect_absent=("vector for",),
        stderr_needles=(
            "[vector-validation] status=skipped reason=hint-not-certifiable-or-non-innermost",
        ),
        stderr_absent=("[alarm]",),
        same_as_args=tuple(JACOBI_FULL_DIAMOND),
    ),
    Check(
        "full-diamond-vector-iss",
        ["--tile", "--smartfuse", "--nointratileopt", "--nounrolljam", "--rar", "--full-diamond-tile", "--noparallel", "--vector", "--iss"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        effect_needles=("32 *", "i4 + (-1 * i5)"),
        effect_absent=("vector for",),
        stderr_needles=(
            "[vector-validation] status=skipped reason=hint-not-certifiable-or-non-innermost",
        ),
        stderr_absent=("[alarm]",),
        same_as_args=tuple(JACOBI_FULL_DIAMOND_ISS),
    ),
    Check(
        "full-diamond-multipar",
        [*FLAGS, "--full-diamond-tile", "--parallel", "--multipar", "--innerpar"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        effect_needles=("parallel for i0", "parallel for i5", "i4 + (-1 * i5)"),
        differs_from_args=(tuple([*FLAGS, "--full-diamond-tile", "--parallel", "--innerpar"]),),
    ),
    Check(
        "full-diamond-multipar-iss",
        [*FLAGS, "--full-diamond-tile", "--parallel", "--multipar", "--innerpar", "--iss"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        effect_needles=("parallel for i0", "parallel for i5", "i4 + (-1 * i5)"),
        differs_from_args=(tuple([*FLAGS, "--full-diamond-tile", "--parallel", "--innerpar", "--iss"]),),
    ),
    Check(
        "full-diamond-second-level",
        [*FLAGS, "--full-diamond-tile", "--noparallel", "--second-level-tile"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --second-level-tile --full-diamond-tile",
        effect_needles=("32 *",),
        tiling_route="permutable-band",
        differs_from_args=(tuple(JACOBI_NODIAMOND), tuple(JACOBI_FULL_DIAMOND)),
    ),
    Check(
        "full-diamond-iss-second-level",
        [*FLAGS, "--full-diamond-tile", "--noparallel", "--iss", "--second-level-tile"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --second-level-tile --full-diamond-tile",
        effect_needles=("32 *",),
        tiling_route="permutable-band",
        differs_from_args=(tuple(JACOBI_NODIAMOND_ISS), tuple(JACOBI_FULL_DIAMOND_ISS)),
    ),
    Check("reject-bare-default", [], MATMUL, False, "Pluto enables --intratileopt by default"),
    Check(
        "prevector",
        MATMUL_TILED_PREVECTOR,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --vector",
        effect_needles=("vector for i5", "32 *", "/ 32"),
        stderr_needles=(
            "[vector-validation] status=applied source=pluto-hint scope=innermost",
        ),
        stderr_absent=("[alarm]",),
        tiling_route="permutable-band",
        differs_from_args=(tuple(MATMUL_TILED),),
    ),
    Check(
        "native-vector",
        ["--tile", "--smartfuse", "--nointratileopt", "--nounrolljam", "--rar", "--nodiamond-tile", "--noparallel", "--vector"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --vector",
        effect_needles=("vector for i5", "32 *", "/ 32"),
        stderr_needles=(
            "[vector-validation] status=applied source=pluto-hint scope=innermost",
        ),
        stderr_absent=("[alarm]",),
        tiling_route="permutable-band",
        differs_from_args=(tuple(MATMUL_TILED),),
    ),
    Check(
        "native-vector-strict-hint-only",
        ["--tile", "--smartfuse", "--nointratileopt", "--nounrolljam", "--rar", "--nodiamond-tile", "--noparallel", "--vector", "--vector-strict"],
        SYMBOLIC_SECOND_LEVEL,
        True,
        "== Optimized Loop ==",
        "polopt args: --vector --vector-strict",
        effect_needles=("vector for", "32 *", "/ 32"),
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--noparallel"]),),
    ),
    Check(
        "default-prevector",
        MATMUL_TILED_DEFAULT_PREVECTOR,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --vector",
        effect_needles=("vector for i5", "32 *", "/ 32"),
        stderr_needles=(
            "[vector-validation] status=applied source=pluto-hint scope=innermost",
        ),
        stderr_absent=("[alarm]",),
        tiling_route="permutable-band",
        differs_from_args=(tuple(MATMUL_TILED),),
    ),
    Check(
        "const-unrolljam-constant-loop",
        ["--notile", "--nointratileopt", "--noprevector", "--unrolljam", "--nodiamond-tile", "--noparallel", "--rar"],
        CONST_UNROLL,
        True,
        "a[3] = 3;",
        "polopt args: --notile --unrolljam",
        effect_absent=("for i0 in range",),
        env={"POLCERT_UNROLLJAM_POLICY": "checked-all-depths"},
    ),
    Check(
        "stride-loop-positive-literal",
        ["--identity", "--notile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel", "--rar"],
        STRIDE_EVEN,
        True,
        "== Optimized Loop ==",
        "polopt args: --identity",
        effect_needles=("for i0 in range(0, ((N + 1) / 2))", "a[(2 * i0)] = ((2 * i0) + 1);"),
    ),
    Check(
        "stride-loop-negative-literal",
        ["--identity", "--notile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel", "--rar"],
        STRIDE_DOWN,
        True,
        "== Optimized Loop ==",
        "polopt args: --identity",
        effect_needles=("for i0 in range(0, ((N + 1) / 2))", "a[(N + ((-2 * i0) + -1))] = (N + ((-2 * i0) + 6));"),
    ),
    Check(
        "reject-stride-zero",
        ["--identity", "--notile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"],
        STRIDE_BAD_ZERO,
        False,
        "range step must be a nonzero integer literal",
    ),
    Check(
        "reject-stride-symbolic",
        ["--identity", "--notile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"],
        STRIDE_BAD_SYMBOLIC,
        False,
        "range step must be a nonzero integer literal",
    ),
    Check(
        "const-unrolljam-ufactor-constant-loop",
        CONST_UNROLL_UFACTOR,
        CONST_UNROLL,
        True,
        "a[3] = 3;",
        "checked post flags: --ufactor=3",
        effect_absent=("for i0 in range",),
        env={"POLCERT_UNROLLJAM_POLICY": "checked-all-depths"},
    ),
    Check(
        "block-unrolljam-ufactor-variable-loop",
        ["--notile", "--nointratileopt", "--noprevector", "--unrolljam", "--ufactor=3", "--nodiamond-tile", "--noparallel", "--rar"],
        SCALPRIV,
        True,
        "for i0 in range(0, (N / 3))",
        "checked post flags: --ufactor=3",
        effect_needles=("b[((3 * i0) + 2)] = a;", "for i0 in range((3 * (N / 3)), N)", "b[i0] = a;"),
        env={"POLCERT_UNROLLJAM_POLICY": "checked-all-depths"},
    ),
    Check(
        "mixed-const-and-block-unrolljam",
        ["--identity", "--notile", "--nointratileopt", "--noprevector", "--unrolljam", "--ufactor=2", "--nodiamond-tile", "--noparallel", "--rar"],
        MIXED_UNROLL,
        True,
        "for i0 in range(0, (N / 2))",
        "checked post flags: --ufactor=2",
        effect_needles=("c[0] = 0;", "c[1] = 1;", "b[((2 * i0) + 1)] = ((2 * i0) + 1);", "for i0 in range((2 * (N / 2)), N)", "b[i0] = i0;"),
        env={"POLCERT_UNROLLJAM_POLICY": "checked-all-depths"},
    ),
    Check(
        "unrolljam-context-bound-escape-rejected",
        ["--identity", "--notile", "--nointratileopt", "--noprevector", "--unrolljam", "--ufactor=2", "--nodiamond-tile", "--noparallel", "--rar"],
        UNROLLJAM_CONTEXT_BOUND_ESCAPE,
        True,
        "for i0 in range(0, ((N + -1) / 2))",
        "checked post flags: --ufactor=2",
        effect_needles=(
            "A[((2 * i0) + 1)][(2 * i1)] = (A[(2 * i0)][K] + 1);",
            "A[((2 * i0) + 2)][(2 * i1)] = (A[((2 * i0) + 1)][K] + 1);",
        ),
        effect_absent=(
            "A[((2 * i0) + 1)][(2 * i1)] = (A[(2 * i0)][K] + 1);\n"
            "          A[((2 * i0) + 2)][(2 * i1)] = (A[((2 * i0) + 1)][K] + 1);",
        ),
        env={"POLCERT_UNROLLJAM_POLICY": "checked-all-depths"},
    ),
    Check(
        "unrolljam-empty-selector-policy",
        ["--tile", "--smartfuse", "--nointratileopt", "--noprevector", "--unrolljam", "--ufactor=4", "--nodiamond-tile", "--noparallel", "--rar"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "checked post flags: --ufactor=4",
        effect_absent=("(4 * i", "+ 3))", " / 4)))"),
        env={"POLCERT_UNROLLJAM_POLICY": "none"},
    ),
    Check(
        "reject-default-prevector-parallel",
        ["--tile", "--smartfuse", "--nointratileopt", "--nounrolljam", "--rar", "--nodiamond-tile", "--parallel"],
        MATMUL,
        False,
        "--prevector/--vector cannot be combined with --parallel",
    ),
    Check(
        "parallel-unrolljam-constant-range",
        ["--notile", "--smartfuse", "--nointratileopt", "--noprevector", "--unrolljam", "--ufactor=2", "--rar", "--nodiamond-tile", "--parallel", "--innerpar"],
        NODEP,
        True,
        "== Optimized Loop ==",
        "parallel for",
        effect_patterns=(
            r"for (?P<unrolled>i[0-9]+) in range\(0, 50\) \{"
            r".*?\(\(2 \* (?P=unrolled)\) \+ 1\)",
        ),
        env={"POLCERT_UNROLLJAM_POLICY": "checked-all-depths"},
    ),
    Check(
        "reject-parallel-unrolljam-symbolic-reannotation",
        ["--tile", "--smartfuse", "--nointratileopt", "--noprevector", "--unrolljam", "--ufactor=3", "--rar", "--nodiamond-tile", "--parallel"],
        MATMUL,
        False,
        "Extractor rejected non-affine SCoP fragment",
        env={"POLCERT_UNROLLJAM_POLICY": "checked-all-depths"},
    ),
    Check(
        "reject-unrolljam-prevector",
        ["--tile", "--smartfuse", "--nointratileopt", "--prevector", "--unrolljam", "--ufactor=3", "--rar", "--nodiamond-tile", "--noparallel"],
        MATMUL,
        False,
        "--unrolljam cannot currently be combined with vector execution",
    ),
    Check(
        "reject-prevector-conflict",
        ["--tile", "--smartfuse", "--nointratileopt", "--prevector", "--noprevector", "--nounrolljam", "--rar", "--nodiamond-tile", "--noparallel"],
        MATMUL,
        False,
        "contradictory vector controls",
    ),
    Check("reject-intratile-conflict", ["--tile", "--intratileopt", "--nointratileopt", "--nodiamond-tile", "--noparallel"], MATMUL, False, "contradictory tile-schedule controls"),
    Check("reject-lastwriter-conflict", ["--notile", "--lastwriter", "--nolastwriter", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "contradictory dependence controls"),
    Check("reject-ft-without-lt", [*FLAGS, "--ft=0", "--nodiamond-tile", "--noparallel"], MATMUL, False, "--ft and --lt must be supplied together"),
    Check("reject-pet", ["--pet", *FLAGS, "--nodiamond-tile", "--noparallel"], MATMUL, False, "frontend is polopt's verified loop extractor"),
    Check("reject-stale-multipipe", ["--multipipe", *MATMUL_TILED], MATMUL, False, "not accepted by the current Pluto binary"),
    Check("reject-stale-lbtile", ["--lbtile", *MATMUL_TILED], MATMUL, False, "not accepted by the current Pluto binary"),
    Check("reject-stale-sched", ["--sched", *MATMUL_TILED], MATMUL, False, "not accepted by the current Pluto binary"),
    Check("reject-stale-variables-not-global", ["--variables_not_global", *MATMUL_TILED], MATMUL, False, "not accepted by the current Pluto binary"),
    Check("reject-stale-output", ["--output", *MATMUL_TILED], MATMUL, False, "current Pluto binary uses -o"),
    Check("reject-unroll-abbrev", ["--unroll", *MATMUL_TILED], MATMUL, False, "use explicit --unrolljam"),
    Check("reject-typedfuse", ["--tile", "--typedfuse", "--nodiamond-tile", "--noparallel"], MATMUL, False, "requires a GLPK- or Gurobi-enabled Pluto binary"),
    Check("reject-scalpriv-without-candldep", ["--notile", "--scalpriv", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "--scalpriv requires --candldep"),
    Check("reject-cache-without-determine", [*FLAGS, "--cache-size=32768", "--nodiamond-tile", "--noparallel"], MATMUL, False, "require --determine-tile-size"),
    Check("reject-ufactor-without-determine-or-unrolljam", [*FLAGS, "--ufactor=3", "--nodiamond-tile", "--noparallel"], MATMUL, False, "requires --unrolljam"),
    Check(
        "reject-ufactor-zero",
        ["--identity", "--notile", "--nointratileopt", "--noprevector", "--unrolljam", "--ufactor=0", "--nodiamond-tile", "--noparallel"],
        MATMUL,
        False,
        "--ufactor: value must be a positive integer",
    ),
    Check(
        "reject-ufactor-nonnumeric",
        ["--identity", "--notile", "--nointratileopt", "--noprevector", "--unrolljam", "--ufactor=abc", "--nodiamond-tile", "--noparallel"],
        MATMUL,
        False,
        "--ufactor: value must be a positive integer",
    ),
    Check(
        "reject-missing-explicit-tile-sizes-file",
        [*MATMUL_TILED, "--tile-sizes-file", "/tmp/polcert-missing-control-file"],
        MATMUL,
        False,
        "no such file",
    ),
    Check("reject-bare-identity", ["--identity", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "use --identity --notile"),
    Check(
        "identity-second-level",
        IDENTITY_TILED_SECOND_LEVEL,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --identity --tile --second-level-tile",
        effect_needles=("/ 256", "8 *", "32 *"),
        tiling_route="permutable-band",
        differs_from_args=(tuple(IDENTITY_TILED),),
    ),
    Check(
        "identity-second-level-matmul-init",
        IDENTITY_TILED_SECOND_LEVEL,
        MATMUL_INIT,
        True,
        "== Optimized Loop ==",
        "polopt args: --identity --tile --second-level-tile",
        effect_needles=("/ 256", "8 *", "32 *"),
        tiling_route="permutable-band",
        differs_from_args=(tuple(IDENTITY_TILED),),
    ),
    Check(
        "identity-second-level-iss",
        IDENTITY_TILED_SECOND_LEVEL_ISS,
        FUSION7,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --identity --tile --second-level-tile",
        effect_needles=("/ 256", "8 *", "32 *"),
        tiling_route="permutable-band",
        differs_from_args=(tuple(["--identity", "--tile", "--iss", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"]),),
    ),
    Check(
        "optimizer-implicit-tile-sizes-file",
        MATMUL_TILED,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: <default>",
        effect_needles=("16 *", "/ 16"),
        differs_from_args=(tuple(MATMUL_TILED),),
        implicit_control_file="tile.sizes",
        implicit_control_file_content="16\n16\n16\n",
    ),
    Check(
        "optimizer-explicit-tile-sizes-file",
        MATMUL_TILED,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto control files: tile.sizes<=",
        effect_needles=("16 *", "/ 16"),
        differs_from_args=(tuple(MATMUL_TILED),),
        explicit_control_flag="--tile-sizes-file",
        explicit_control_file_content="16\n16\n16\n",
    ),
    Check(
        "optimizer-explicit-tile-sizes-file-nodep",
        MATMUL_TILED,
        NODEP,
        True,
        "== Optimized Loop ==",
        "pluto control files: tile.sizes<=",
        effect_needles=("for i0 in range(0, 13)", "8 *"),
        differs_from_args=(tuple(MATMUL_TILED),),
        explicit_control_flag="--tile-sizes-file",
        explicit_control_file_content="8\n8\n8\n",
    ),
    Check(
        "optimizer-implicit-fst-file",
        FUSION_NOTILE_SMART,
        FUSION1,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse",
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
        implicit_control_file=".fst",
        implicit_control_file_content="2\n1\n0\n0\n1\n1\n0\n",
    ),
    Check(
        "optimizer-explicit-fst-file",
        FUSION_NOTILE_SMART,
        FUSION1,
        True,
        "== Optimized Loop ==",
        "pluto control files: .fst<=",
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
        explicit_control_flag="--fusion-structure",
        explicit_control_file_content="2\n1\n0\n0\n1\n1\n0\n",
    ),
    Check(
        "optimizer-explicit-fst-file-fusion2",
        FUSION_NOTILE_SMART,
        FUSION2,
        True,
        "== Optimized Loop ==",
        "pluto control files: .fst<=",
        effect_needles=("for i1 in range(i0, (i0 + 100))",),
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
        explicit_control_flag="--fusion-structure",
        explicit_control_file_content="2\n1\n0\n0\n1\n1\n0\n",
    ),
    Check(
        "optimizer-implicit-precut-file",
        FUSION_NOTILE_SMART,
        FUSION1,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse",
        effect_needles=("if (4 <= N)", "if (6 <= N)"),
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
        implicit_control_file=".precut",
        implicit_control_file_content="2\n1\n2 4\n0 0 0 0\n0 1 0 0\n1\n0\n2 4\n0 0 0 1\n0 1 0 0\n1\n0\n",
    ),
    Check(
        "reject-implicit-skipdeps-file",
        MATMUL_NOTILE,
        MATMUL,
        False,
        "implicit Pluto control file skipdeps.txt is not supported by polopt",
        implicit_control_file="skipdeps.txt",
        implicit_control_file_content="1\n",
    ),
    Check(
        "reject-implicit-codegen-context-file",
        MATMUL_NOTILE,
        MATMUL,
        False,
        "implicit Pluto control file codegen.context is not supported by polopt",
        implicit_control_file="codegen.context",
        implicit_control_file_content="0\n",
    ),
    Check(
        "reject-implicit-linearized-file",
        MATMUL_NOTILE,
        MATMUL,
        False,
        "implicit Pluto control file .linearized is not supported by polopt",
        implicit_control_file=".linearized",
        implicit_control_file_content="replacement statement\n",
    ),
    Check(
        "reject-implicit-nonlinearized-file",
        MATMUL_NOTILE,
        MATMUL,
        False,
        "implicit Pluto control file .nonlinearized is not supported by polopt",
        implicit_control_file=".nonlinearized",
        implicit_control_file_content="original statement\n",
    ),
    Check(
        "optimizer-explicit-precut-file",
        FUSION_NOTILE_SMART,
        FUSION1,
        True,
        "== Optimized Loop ==",
        "pluto control files: .precut<=",
        effect_needles=("if (4 <= N)", "if (6 <= N)"),
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
        explicit_control_flag="--precut-file",
        explicit_control_file_content="2\n1\n2 4\n0 0 0 0\n0 1 0 0\n1\n0\n2 4\n0 0 0 1\n0 1 0 0\n1\n0\n",
    ),
    Check(
        "optimizer-explicit-precut-file-fusion2",
        FUSION_NOTILE_SMART,
        FUSION2,
        True,
        "== Optimized Loop ==",
        "pluto control files: .precut<=",
        effect_needles=("for i1 in range(0, 100)", "B[i0][i1]"),
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
        explicit_control_flag="--precut-file",
        explicit_control_file_content="2\n1\n2 4\n0 0 0 0\n0 1 0 0\n1\n0\n2 4\n0 0 0 1\n0 1 0 0\n1\n0\n",
    ),
    Check(
        "identity-tiled",
        IDENTITY_TILED,
        FUSION7,
        True,
        "== Optimized Loop ==",
        "polopt args: --identity --tile",
        effect_needles=("32 *", "/ 32"),
        differs_from_args=(tuple(["--identity", "--notile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"]),),
    ),
    Check(
        "identity-tiled-mixed-depth",
        IDENTITY_TILED,
        MATMUL_INIT,
        True,
        "== Optimized Loop ==",
        "polopt args: --identity --tile",
        effect_needles=("32 *", "/ 32"),
        tiling_route="permutable-band",
        differs_from_args=(tuple(["--identity", "--notile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"]),),
    ),
    Check(
        "identity-tiled-mixed-depth-iss",
        [*IDENTITY_TILED, "--iss"],
        MATMUL_INIT,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --identity --tile",
        effect_needles=("32 *", "/ 32"),
        tiling_route="permutable-band",
        differs_from_args=(tuple(["--identity", "--notile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"]),),
    ),
    Check(
        "identity-tiled-parallel",
        IDENTITY_TILED_PARALLEL,
        MATMUL_INIT,
        True,
        "== Optimized Loop ==",
        "polopt args: --identity --tile --parallel",
        effect_needles=("parallel for i0", "32 *", "/ 32"),
        tiling_route="permutable-band",
        differs_from_args=(tuple(IDENTITY_TILED),),
    ),
    Check(
        "identity-tiled-parallel-strict-hint-only",
        [*IDENTITY_TILED_PARALLEL, "--parallel-strict"],
        MATMUL_INIT,
        True,
        "== Optimized Loop ==",
        "polopt args: --identity --tile --parallel --parallel-strict",
        effect_needles=("parallel for i0", "32 *", "/ 32"),
        tiling_route="permutable-band",
        differs_from_args=(tuple(IDENTITY_TILED),),
    ),
    Check(
        "identity-tiled-vector-strict-hint-only",
        ["--identity", "--tile", "--vector", "--vector-strict", "--nointratileopt", "--nounrolljam", "--nodiamond-tile", "--noparallel", "--rar"],
        MATMUL_INIT,
        True,
        "== Optimized Loop ==",
        "polopt args: --identity --tile --vector --vector-strict",
        effect_needles=("32 *", "/ 32"),
        effect_absent=("vector for",),
        stderr_needles=(
            "[vector-validation] status=skipped "
            "reason=hint-not-certifiable-or-non-innermost",
        ),
        stderr_absent=("[alarm]",),
        tiling_route="permutable-band",
    ),
    Check(
        "identity-tiled-vector-strict-valid-hint",
        ["--identity", "--tile", "--vector", "--vector-strict", "--nointratileopt", "--nounrolljam", "--nodiamond-tile", "--noparallel", "--rar"],
        SYMBOLIC_SECOND_LEVEL,
        True,
        "== Optimized Loop ==",
        "polopt args: --identity --tile --vector --vector-strict",
        effect_needles=("vector for i3", "32 *", "/ 32"),
        stderr_needles=(
            "[vector-validation] status=applied source=pluto-hint scope=innermost",
        ),
        stderr_absent=("[alarm]",),
        tiling_route="permutable-band",
    ),
    Check(
        "identity-tiled-multipar",
        IDENTITY_TILED_MULTIPAR,
        MATMUL_INIT,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --multipar",
        effect_needles=("parallel for i0", "parallel for i1", "32 *", "/ 32"),
        tiling_route="permutable-band",
        differs_from_args=(tuple(IDENTITY_TILED_PARALLEL),),
    ),
    Check(
        "identity-tiled-multipar-strict-hint-only",
        [*IDENTITY_TILED_MULTIPAR, "--parallel-strict"],
        MATMUL_INIT,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --multipar",
        effect_needles=("parallel for i0", "32 *", "/ 32"),
        effect_absent=("parallel for i1",),
        tiling_route="permutable-band",
        differs_from_args=(tuple(IDENTITY_TILED_MULTIPAR),),
    ),
    Check(
        "identity-tiled-iss",
        ["--identity", "--tile", "--iss", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel", "--rar"],
        FUSION7,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --identity --tile",
        effect_needles=("32 *", "/ 32"),
        differs_from_args=(tuple(["--identity", "--notile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel", "--rar"]),),
    ),
    Check("reject-tile-notile", [*FLAGS, "--tile", "--notile", "--nodiamond-tile", "--noparallel"], MATMUL, False, "--tile and --notile are both present"),
    Check("reject-diamond-nodiamond", [*FLAGS, "--diamond-tile", "--nodiamond-tile", "--noparallel"], MATMUL, False, "--diamond-tile/--full-diamond-tile and --nodiamond-tile are both present"),
]


def pluto_help_text() -> str:
    pluto = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"))
    try:
        proc = subprocess.run(
            [str(pluto), "--help"],
            text=True,
            capture_output=True,
            timeout=10,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ""
    return proc.stdout + proc.stderr


def pluto_supports_option(flag: str) -> bool:
    return flag in pluto_help_text()


def pluto_has_lp_solver_support() -> bool:
    help_text = pluto_help_text()
    return "--glpk" in help_text or "--gurobi" in help_text


def active_checks() -> list[Check]:
    checks = list(CHECKS)
    if pluto_has_lp_solver_support():
        checks = [check for check in checks if check.name != "reject-typedfuse"]
        checks.extend(
            [
                Check(
                    "optimizer-glpk-affine",
                    TUNING_NOTILE_GLPK,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk",
                    effect_needles=("for i0 in range(0, M)", "A[i0][i2]"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-ilp-affine",
                    TUNING_NOTILE_ILP,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --ilp",
                    effect_needles=("for i0 in range(0, M)", "A[i0][i2]"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-lp-affine",
                    TUNING_NOTILE_LP,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --lp",
                    effect_needles=("for i0 in range(0, M)", "A[i0][i2]"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-lpcolor-affine",
                    TUNING_NOTILE_LPCOLOR,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --lpcolor",
                    effect_needles=("for i0 in range(0, M)", "A[i0][i2]"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-dfp-affine",
                    TUNING_NOTILE_DFP,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --dfp",
                    effect_needles=("for i1 in range(i0, (N + i0))", "(-1 * i0)"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-clusterscc-affine",
                    TUNING_NOTILE_CLUSTERSCC,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --clusterscc",
                    effect_needles=("for i0 in range(0, M)", "A[i0][i2]"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-hybridfuse-affine",
                    TUNING_NOTILE_HYBRIDFUSE,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --hybridfuse",
                    effect_needles=("for i1 in range(i0, (N + i0))", "(-1 * i0)"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-delayedcut-affine",
                    TUNING_NOTILE_DELAYEDCUT,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --dfp --delayedcut",
                    effect_needles=("for i1 in range(i0, (N + i0))", "(-1 * i0)"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-typedfuse-affine",
                    TUNING_NOTILE_TYPEDFUSE,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --typedfuse --glpk",
                    effect_needles=("for i1 in range(i0, (N + i0))", "(-1 * i0)"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-dfp-corcol-effect",
                    TUNING_NOTILE_DFP,
                    CORCOL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --dfp",
                    effect_needles=("if ((1 <= N && 2 <= M))", "symmat[i1][i0] = symmat[i0][i1];"),
                    differs_from_args=(tuple(TUNING_NOTILE_GLPK),),
                ),
                Check(
                    "optimizer-typedfuse-adi-effect",
                    TUNING_NOTILE_TYPEDFUSE,
                    ADI,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --typedfuse --glpk",
                    effect_needles=("for i1 in range(0, N)", "X[i2][i1]"),
                    differs_from_args=(tuple(TUNING_NOTILE_GLPK),),
                ),
                Check(
                    "optimizer-hybridfuse-adi-effect",
                    TUNING_NOTILE_HYBRIDFUSE,
                    ADI,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --hybridfuse",
                    effect_needles=("for i1 in range(0, N)", "X[i2][i1]"),
                    differs_from_args=(tuple(TUNING_NOTILE_GLPK),),
                ),
                Check(
                    "optimizer-delayedcut-corcol-effect",
                    TUNING_NOTILE_DELAYEDCUT,
                    CORCOL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --dfp --delayedcut",
                    effect_needles=("if ((1 <= N && 2 <= M))", "symmat[i1][i0] = symmat[i0][i1];"),
                    differs_from_args=(tuple(TUNING_NOTILE_GLPK),),
                ),
            ]
        )
    else:
        checks.extend(
            [
                Check("reject-glpk-without-solver-build", ["--notile", "--glpk", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "does not advertise this LP/DFP option"),
                Check("reject-lp-without-solver-build", ["--notile", "--lp", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "does not advertise this LP/DFP option"),
            ]
        )
    if compat.pluto_has_working_candldep():
        checks.extend(
            [
                Check(
                    "optimizer-candldep-affine",
                    TUNING_NOTILE_CANDLDEP,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --candldep",
                ),
                Check(
                    "optimizer-candldep-scalpriv-affine",
                    TUNING_NOTILE_CANDLDEP_SCALPRIV,
                    SCALPRIV,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --candldep --scalpriv",
                    effect_needles=("b[i0] = a",),
                ),
                Check(
                    "optimizer-candldep-scalpriv-parallel-conservative",
                    TUNING_NOTILE_CANDLDEP_SCALPRIV_PARALLEL,
                    SCALPRIV,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --candldep --scalpriv",
                    effect_needles=("b[i0] = a",),
                    effect_absent=("parallel for",),
                    stderr_needles=(
                        "[parallel-validation] status=skipped source=pluto-hint "
                        "reason=no-certifiable-dimension",
                    ),
                ),
                Check(
                    "reject-candldep-lastwriter",
                    ["--notile", "--smartfuse", "--candldep", "--lastwriter", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"],
                    REG_MATMUL,
                    False,
                    "--lastwriter is only supported with Pluto's ISL dependence tester",
                ),
                Check(
                    "reject-isldep-candldep",
                    ["--notile", "--smartfuse", "--isldep", "--candldep", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"],
                    REG_MATMUL,
                    False,
                    "--isldep and --candldep are both present",
                ),
            ]
        )
    else:
        checks.append(
            Check(
                "reject-candldep-broken-importer",
                ["--notile", "--candldep", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"],
                MATMUL,
                False,
                "selected Pluto Candl importer aborts on a dependent probe",
            )
        )
    return checks


ROUTE_BINDINGS = {
    ("syntax/SLoopMain.ml", "module VerifiedParallelCompiler = SVerifiedParallelCompilerConfig"):
        "normal end-to-end routes must expose the extracted Loop-to-ParallelLoop compiler dispatcher",
    ("syntax/SLoopMain.ml", "VerifiedParallelCompiler.compile"):
        "normal end-to-end optimization must call the extracted Loop-to-ParallelLoop compiler dispatcher",
    ("syntax/SVerifiedParallelCompilerConfig.v", "| VSeq seq_cfg =>"):
        "sequential routes must be lifted into the unified ParallelLoop dispatcher",
    ("syntax/SVerifiedParallelCompilerConfig.v", "checked_lift_sequential_loop loop"):
        "sequential routes must be checked-lifted before entering the ParallelLoop output surface",
    ("syntax/SVerifiedParallelCompilerConfig.v", "| VParallelCurrentDefault d =>"):
        "parallel-current routes must be represented in the unified extracted dispatcher",
    ("syntax/SLoopMain.ml", "module VerifiedSequentialCompiler = SVerifiedCompilerConfig"):
        "sequential Loop routes used by post-codegen checks must still have the extracted verified dispatcher available",
    ("syntax/SLoopMain.ml", "VerifiedSequentialCompiler.compile"):
        "sequential post-codegen routes must still call the extracted verified compiler dispatcher",
    ("syntax/SVerifiedCompilerConfig.v", "| VDefaultBand => SBandTilingOpt.opt loop"):
        "default sequential route must use the extracted band-aware optimizer",
    ("syntax/SVerifiedCompilerConfig.v", "| VDefault => SBandTilingOpt.opt loop"):
        "the public RawDefault compatibility config must also be band-first",
    ("syntax/SVerifiedCompilerConfig.v", "| VPostTilingAffine => SBandTilingOpt.opt_post_tiling_affine loop"):
        "diamond route must use the extracted SBandTilingOpt.opt_post_tiling_affine entry",
    ("syntax/SVerifiedCompilerConfig.v", "| VPostTilingAffineISS => SBandTilingOpt.opt_post_tiling_affine_with_iss loop"):
        "diamond+ISS route must use the extracted SBandTilingOpt.opt_post_tiling_affine_with_iss entry",
    ("syntax/SVerifiedCompilerConfig.v", "| VIdentity => SPolOpt.opt_identity loop"):
        "identity route must use the extracted SPolOpt.opt_identity entry",
    ("syntax/SVerifiedCompilerConfig.v", "| VSecondLevel => SBandTilingOpt.opt loop"):
        "second-level tiling must use the unified band-first optimizer",
    ("syntax/SVerifiedCompilerConfig.v", "| VSecondLevelISS => SBandTilingOpt.opt_with_iss loop"):
        "ISS second-level tiling must use the unified band-first optimizer",
    ("syntax/SVerifiedCompilerConfig.v", "| VISS => SBandTilingOpt.opt_with_iss loop"):
        "ordinary ISS tiling must use the unified band-first optimizer",
    ("syntax/SVerifiedCompilerConfig.v", "| VIdentitySecondLevel => SBandTilingOpt.opt_identity_tiled loop"):
        "second-level identity tiling must use the unified band-first entry",
    ("syntax/SVerifiedCompilerConfig.v", "| VIdentityBand => SBandTilingOpt.opt_identity_tiled loop"):
        "ordinary identity tiling must still use the extracted band-aware theorem-facing entry",
    ("syntax/SVerifiedCompilerConfig.v", "| VIdentitySecondLevelISS =>"):
        "ISS second-level identity tiling must be represented in the extracted dispatcher",
    ("syntax/SVerifiedCompilerConfig.v", "SBandTilingOpt.opt_identity_tiled_with_iss loop"):
        "ISS second-level identity tiling must use the unified band-first entry",
    ("syntax/SVerifiedCompilerConfig.v", "| VIdentityBandISS => SBandTilingOpt.opt_identity_tiled_with_iss loop"):
        "ordinary ISS identity tiling must still use the extracted band-aware theorem-facing entry",
    ("syntax/SLoopMain.ml", "let selection = validate_flag_model Sys.argv.(0) cfg"):
        "the driver must retain the normalized route selection",
    ("syntax/SLoopMain.ml", "configure_scheduler_modes selection cfg"):
        "scheduler modes must be configured from the normalized route selection",
    ("syntax/SLoopMain.ml", "match route.SLoopRoute.execution_family with"):
        "final execution dispatch must use the normalized route",
    ("syntax/SLoopMain.ml", "route_uses_post_tiling_affine route"):
        "intratile and diamond routes must select the proved post-tiling affine composition",
    ("syntax/SLoopMain.ml", "RawParallelCurrentIdentityTiled d"):
        "explicit-current identity tiling route must use the unified theorem-facing compiler config",
}

FORBIDDEN_ROUTE_BINDINGS = {
    ("syntax/SLoopMain.ml", "SLoopDispatch.run_selected_optimization cfg sequential_handlers loop"):
        "normal sequential optimization must not bypass SVerifiedCompilerConfig",
    ("syntax/SLoopMain.ml", "let sequential_handlers ="):
        "the old sequential handler table should not remain as the normal dispatch path",
    ("syntax/SLoopMain.ml", "let hinted_parallel_handlers ="):
        "the old hinted-parallel handler table must not be reconnectable",
    ("syntax/SLoopMain.ml", "let current_parallel_handlers ="):
        "the old explicit-current handler table must not be reconnectable",
    ("syntax/SVerifiedCompilerConfig.v", "SPolOpt.opt_identity_tiled_generic"):
        "second-level identity tiling must not bypass the unified band-first route",
    ("syntax/SVerifiedCompilerConfig.v", "| VDefault => SPolOpt.opt loop"):
        "the public RawDefault compatibility config must not bypass band-first validation",
    ("syntax/SLoopMain.ml", "cfg.force_identity"):
        "normalized schedule selection must not be bypassed by raw CLI booleans",
    ("syntax/SLoopMain.ml", "cfg.force_notile"):
        "normalized tiling selection must not be bypassed by raw CLI booleans",
    ("syntax/SLoopMain.ml", "cfg.force_iss"):
        "normalized ISS selection must not be bypassed by raw CLI booleans",
    ("syntax/SLoopMain.ml", "cfg.force_diamond_tile"):
        "normalized tiling shape must not be bypassed by raw CLI booleans",
    ("syntax/SLoopMain.ml", "cfg.pluto_intratileopt_seen"):
        "normalized intratile policy must not be bypassed by raw CLI booleans",
}


TILING_FLAGS = {
    "--tile",
    "--second-level-tile",
    "--diamond-tile",
    "--full-diamond-tile",
}


def has_tiling_phase(check: Check) -> bool:
    return check.success and any(flag in check.args for flag in TILING_FLAGS)


def check_route_bindings() -> list[str]:
    failures = []
    for needle, reason in ROUTE_BINDINGS.items():
        if isinstance(needle, tuple):
            relpath, pattern = needle
        else:
            relpath, pattern = "syntax/SLoopMain.ml", needle
        source = (ROOT / relpath).read_text()
        if pattern not in source:
            failures.append(f"route binding missing in {relpath}: {pattern!r}; {reason}")
    for (relpath, pattern), reason in FORBIDDEN_ROUTE_BINDINGS.items():
        source = (ROOT / relpath).read_text()
        if pattern in source:
            failures.append(f"forbidden route binding in {relpath}: {pattern!r}; {reason}")
    for check in CHECKS:
        if has_tiling_phase(check) and check.needle != "== Optimized Loop ==":
            failures.append(
                f"tiling route check {check.name!r} must be a final optimized-loop check"
            )
        if check.tiling_route is not None and not has_tiling_phase(check):
            failures.append(
                f"non-tiling check {check.name!r} declares route {check.tiling_route!r}"
            )
        if check.name.startswith("default-no-rar-") and oracle_policy(check) != "default-no-rar":
            failures.append(
                f"default-policy check {check.name!r} must omit --rar"
            )
    for check in CHECKS:
        if (
            check.success
            and not check.native
            and not check.name.startswith("default-no-rar-")
            and oracle_policy(check) != "explicit-rar"
        ):
            failures.append(
                f"historical success check {check.name!r} must retain explicit --rar"
            )
    return failures


def optimized_loop(output: str) -> str:
    marker = "== Optimized Loop =="
    pos = output.find(marker)
    if pos < 0:
        return output
    return output[pos:]


def scheduled_openscop(output: str) -> str:
    marker = "== Scheduled OpenScop =="
    start = output.find(marker)
    if start < 0:
        return ""
    end = output.find("== Optimized Loop ==", start)
    return output[start:] if end < 0 else output[start:end]


def reported_oracle_flags(output: str) -> list[list[str]]:
    marker = "pluto oracle flags:"
    return [
        line.partition(marker)[2].strip().split()
        for line in output.splitlines()
        if marker in line
    ]


def run_polopt_compat(
    args: list[str],
    fixture: Path,
    timeout: int,
    cwd: Path = ROOT,
    env_extra: dict[str, str] | None = None,
    native: bool = False,
) -> subprocess.CompletedProcess[str]:
    mode_args = [] if native else ["--pluto-compat", "--explain"]
    cmd = [str(POLOPT), *mode_args, *args, str(fixture)]
    env = os.environ.copy()
    env.setdefault("COMPCERT_CONFIG", str(ROOT / "tests" / "pluto" / "polcert.ini"))
    if env_extra:
        env.update(env_extra)
    return subprocess.run(cmd, cwd=str(cwd), env=env, text=True, capture_output=True, timeout=timeout + 5, check=False)


def explicit_control_target(flag: str | None) -> str | None:
    if flag is None:
        return None
    if flag == "--tile-sizes-file":
        return "tile.sizes"
    if flag in ("--fusion-structure", "--fst-file"):
        return ".fst"
    if flag in ("--precut", "--precut-file"):
        return ".precut"
    return None


def run_check(check: Check, timeout: int) -> str | None:
    control_target = explicit_control_target(check.explicit_control_flag)
    if check.explicit_control_flag:
        with tempfile.TemporaryDirectory(prefix="polopt-compat-explicit-") as tmp:
            control_path = Path(tmp) / "control.in"
            control_path.write_text(check.explicit_control_file_content)
            try:
                proc = run_polopt_compat(
                    [*check.args, check.explicit_control_flag, str(control_path)],
                    check.fixture,
                    timeout,
                    env_extra=check.env,
                    native=check.native,
                )
            except subprocess.TimeoutExpired:
                return f"{check.name}: native polopt compatibility mode timed out"
    elif check.implicit_control_file:
        with tempfile.TemporaryDirectory(prefix="polopt-compat-") as tmp:
            cwd = Path(tmp)
            (cwd / check.implicit_control_file).write_text(check.implicit_control_file_content)
            try:
                proc = run_polopt_compat(check.args, check.fixture, timeout, cwd=cwd, env_extra=check.env, native=check.native)
            except subprocess.TimeoutExpired:
                return f"{check.name}: native polopt compatibility mode timed out"
    else:
        try:
            proc = run_polopt_compat(check.args, check.fixture, timeout, env_extra=check.env, native=check.native)
        except subprocess.TimeoutExpired:
            return f"{check.name}: native polopt compatibility mode timed out"
    output = proc.stdout + proc.stderr
    optimized = optimized_loop(proc.stdout)
    scheduled = scheduled_openscop(proc.stdout)
    if control_target is not None and (ROOT / control_target).exists():
        return (
            f"{check.name}: explicit control file target {control_target!r} "
            "was left in the repository root after the oracle run"
        )
    if check.success:
        if proc.returncode != 0:
            return f"{check.name}: expected success, got exit {proc.returncode}\n{output}"
        if not check.native:
            actual_oracle_flags = reported_oracle_flags(output)
            if not actual_oracle_flags:
                return f"{check.name}: missing reported Pluto oracle flags\n{output}"
            policy = oracle_policy(check)
            if policy == "default-no-rar" and any(
                "--rar" in flags for flags in actual_oracle_flags
            ):
                return (
                    f"{check.name}: default policy unexpectedly invoked Pluto with --rar: "
                    f"{actual_oracle_flags!r}\n{output}"
                )
            if policy == "explicit-rar" and any(
                "--rar" not in flags for flags in actual_oracle_flags
            ):
                return (
                    f"{check.name}: explicit policy omitted --rar from a Pluto invocation: "
                    f"{actual_oracle_flags!r}\n{output}"
                )
        if check.needle not in output:
            return f"{check.name}: missing {check.needle!r}\n{output}"
        if check.normalized is not None and check.normalized not in output:
            return f"{check.name}: missing normalized mapping {check.normalized!r}\n{output}"
        for needle in check.effect_needles:
            if needle not in optimized:
                return f"{check.name}: missing optimization effect marker {needle!r}\n{output}"
        for pattern in check.effect_patterns:
            if re.search(pattern, optimized, re.DOTALL) is None:
                return f"{check.name}: missing optimization effect pattern {pattern!r}\n{output}"
        for needle in check.effect_absent:
            if needle in optimized:
                return f"{check.name}: unexpected optimization marker {needle!r}\n{output}"
        for needle in check.scheduled_needles:
            if needle not in scheduled:
                return f"{check.name}: missing scheduled OpenScop marker {needle!r}\n{output}"
        for needle in check.scheduled_absent:
            if needle in scheduled:
                return f"{check.name}: unexpected scheduled OpenScop marker {needle!r}\n{output}"
        for needle in check.stderr_needles:
            if needle not in proc.stderr:
                return f"{check.name}: missing stderr marker {needle!r}\n{output}"
        for needle in check.stderr_absent:
            if needle in proc.stderr:
                return f"{check.name}: unexpected stderr marker {needle!r}\n{output}"
        if "--second-level-tile" in check.args:
            is_diamond = (
                "--diamond-tile" in check.args
                or "--full-diamond-tile" in check.args
            )
            nested_markers = check.second_level_markers
            if nested_markers is None:
                nested_markers = ("32 *",) if is_diamond else ("/ 256", "8 *", "32 *")
            for marker in nested_markers:
                if marker not in optimized:
                    return f"{check.name}: missing nested second-level tile marker {marker!r}\n{output}"
        if has_tiling_phase(check):
            route_name = check.tiling_route or "permutable-band"
            route_marker = f"[tiling-validation] route={route_name}"
            if "fallback" in output.lower():
                return f"{check.name}: tiling output contains a fallback marker\n{output}"
            route_lines = [
                line.strip()
                for line in proc.stderr.splitlines()
                if line.strip().startswith("[tiling-validation] route=")
            ]
            if route_lines != [route_marker]:
                return f"{check.name}: expected only {route_marker!r}, got {route_lines!r}\n{output}"
            if route_name != "rejected" and "[alarm]" in proc.stderr:
                return f"{check.name}: tiling reported an alarm\n{output}"
        for baseline_args in check.differs_from_args:
            try:
                baseline = run_polopt_compat(list(baseline_args), check.fixture, timeout, native=check.native)
            except subprocess.TimeoutExpired:
                return f"{check.name}: baseline comparison timed out for args {list(baseline_args)!r}"
            baseline_output = baseline.stdout + baseline.stderr
            if baseline.returncode != 0:
                return (
                    f"{check.name}: baseline comparison command failed with exit {baseline.returncode} "
                    f"for args {list(baseline_args)!r}\n{baseline_output}"
                )
            if optimized_loop(baseline.stdout) == optimized:
                return f"{check.name}: optimized loop did not differ from baseline args {list(baseline_args)!r}\n{output}"
        if check.same_as_args is not None:
            try:
                baseline = run_polopt_compat(list(check.same_as_args), check.fixture, timeout, native=check.native)
            except subprocess.TimeoutExpired:
                return f"{check.name}: baseline equality comparison timed out for args {list(check.same_as_args)!r}"
            baseline_output = baseline.stdout + baseline.stderr
            if baseline.returncode != 0:
                return (
                    f"{check.name}: baseline equality command failed with exit {baseline.returncode} "
                    f"for args {list(check.same_as_args)!r}\n{baseline_output}"
                )
            if optimized_loop(baseline.stdout) != optimized:
                return f"{check.name}: optimized loop differed from baseline args {list(check.same_as_args)!r}\n{output}"
    else:
        if proc.returncode == 0:
            return f"{check.name}: expected rejection, but command succeeded\n{output}"
        if check.needle not in output:
            return f"{check.name}: missing rejection reason {check.needle!r}\n{output}"
    return None


def effect_contract_count(check: Check) -> int:
    contracts = (
        len(check.effect_needles)
        + len(check.effect_patterns)
        + len(check.effect_absent)
        + len(check.scheduled_needles)
        + len(check.scheduled_absent)
        + len(check.differs_from_args)
        + (1 if check.same_as_args is not None else 0)
    )
    if "--second-level-tile" in check.args:
        contracts += len(check.second_level_markers or ("auto-second-level-shape",))
    return contracts


def effect_contract_summary(check: Check) -> str:
    contracts = effect_contract_count(check)
    route = check.tiling_route or ("permutable-band" if has_tiling_phase(check) else "none")
    return f"effects={contracts},tiling-route={route}"


def oracle_policy(check: Check) -> str:
    if not check.success:
        return "not-applicable"
    if check.native:
        return "native"
    if "--rar" in check.args:
        return "explicit-rar"
    return "default-no-rar"


def main(argv: list[str]) -> int:
    timeout = 30
    only: set[str] | None = None
    i = 0
    while i < len(argv):
        if argv[i] == "--timeout" and i + 1 < len(argv):
            timeout = int(argv[i + 1])
            i += 2
        elif argv[i] == "--only" and i + 1 < len(argv):
            only = set(argv[i + 1].split(","))
            i += 2
        else:
            print(
                "Usage: run_pluto_compat_suite.py [--timeout SECONDS] [--only NAME,...]",
                file=sys.stderr,
            )
            return 2

    failures = check_route_bindings()
    if not POLOPT.exists():
        print(f"[pluto-compat-suite] missing polopt: {POLOPT}", file=sys.stderr)
        return 2
    checks = active_checks()
    if only is not None:
        checks = [check for check in checks if check.name in only]
        missing_names = sorted(only - {check.name for check in checks})
        if missing_names:
            print(
                "[pluto-compat-suite] unknown checks: " + ", ".join(missing_names),
                file=sys.stderr,
            )
            return 2
    missing = [check.fixture for check in checks if not check.fixture.exists()]
    if missing:
        print("[pluto-compat-suite] missing fixtures:", file=sys.stderr)
        for path in missing:
            print(path, file=sys.stderr)
        return 2
    for check in checks:
        failure = run_check(check, timeout)
        expected_result = "success" if check.success else "rejection"
        actual_result = expected_result if failure is None else "contract-mismatch"
        effect_contracts = effect_contract_count(check)
        coverage = (
            "effect"
            if check.success and effect_contracts > 0
            else "rejection-contract"
            if not check.success
            else "acceptance-only"
        )
        if failure is not None:
            interpretation = "declared-route-or-effect-did-not-match"
        elif coverage == "effect":
            interpretation = "route-and-optimization-contract-matched"
        elif coverage == "rejection-contract":
            interpretation = "unsupported-route-rejected-as-declared"
        else:
            interpretation = "route-accepted-no-specific-effect-asserted"
        if failure is not None:
            actual_summary = "contract-mismatch"
        elif coverage == "effect":
            actual_summary = f"{actual_result},effect-contracts-matched"
        elif coverage == "rejection-contract":
            actual_summary = "rejection,reason-matched"
        else:
            actual_summary = "route-accepted,effect-contracts=none"
        print(
            f"[pluto-compat-suite] {'PASS' if failure is None else 'FAIL'} "
            f"case={check.name} expected={expected_result},{effect_contract_summary(check)} "
            f"oracle-policy={oracle_policy(check)} "
            f"coverage={coverage} "
            f"actual={actual_summary} "
            f"interpretation={interpretation}",
            flush=True,
        )
        if failure is not None:
            failures.append(failure)

    if failures:
        print("[pluto-compat-suite] FAIL")
        for failure in failures:
            print(failure)
        return 1
    policy_counts = {
        policy: sum(oracle_policy(check) == policy for check in checks)
        for policy in ("explicit-rar", "default-no-rar", "native", "not-applicable")
    }
    print(
        f"[pluto-compat-suite] PASS expected={len(checks)} actual={len(checks)} "
        f"explicit-rar={policy_counts['explicit-rar']} "
        f"default-no-rar={policy_counts['default-no-rar']} "
        f"native={policy_counts['native']} "
        f"not-applicable={policy_counts['not-applicable']} "
        "interpretation=all-driver-route-and-effect-contracts-matched"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
