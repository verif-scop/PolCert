#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools" / "polopt_flag_suites"))

import pluto_compat_driver as compat  # noqa: E402
import run_pluto_compat_suite as compat_suite  # noqa: E402


@dataclass(frozen=True)
class Capability:
    request: str
    status: str
    reason: str
    evidence: str
    next_step: str


SUPPORTED = [
    Capability("default tiled route", "supported", "extracted checked affine plus ordinary/second-level tiling route", "strict suite; pluto-compat ordinary-tiled; PolOptBandTiling Opt_band_correct", "keep as baseline"),
    Capability("--notile", "supported", "extracted affine-only checked route, with a separate checked ISS composition when --iss is selected", "pluto-compat affine-only and sequential-iss-notile; Affine_opt_prepared_correct; Opt_with_iss_correct", "keep"),
    Capability("--identity --notile", "supported", "extracted no-Pluto identity extraction/codegen route", "pluto-compat identity-notile; Identity_opt_prepared_correct", "keep"),
    Capability("--identity --tile", "supported-narrow", "checked identity schedule plus tile-only Pluto route; gives a tiling effect when the source-order band is directly tileable", "pluto-compat identity-tiled; Opt_identity_tiled_band_correct", "add composed identity-tile routes only when they map to an extracted theorem-facing pass"),
    Capability("--identity --tile --iss", "supported-narrow", "checked ISS complete-cut split composed with the checked identity-tiling route; current fixture demonstrates the tiling effect under the ISS flag, and bounded exploration found no ISS-only or ISS-different case in the regression corpus", "pluto-compat identity-tiled-iss; Opt_identity_tiled_band_with_iss_correct; identity-composition ISS-sensitive search over 63 regression fixtures", "revisit only if a new Pluto/input corpus exposes a distinct ISS-sensitive identity-tiling effect"),
    Capability("--identity --tile --second-level-tile", "supported-narrow", "the direct permutable-band dispatcher validates Pluto's second-level tile-only output and regenerates the outer-first 256/32 loop shape", "pluto-compat identity-second-level and identity-second-level-matmul-init; identity-composition fusion7 support/effect probe; Opt_identity_tiled_band_correct", "broaden further beyond directly tileable identity bands"),
    Capability("--identity --tile --iss --second-level-tile", "supported-narrow", "checked ISS complete-cut validation composes with the same direct permutable-band identity-tiling route", "pluto-compat identity-second-level-iss; Opt_identity_tiled_band_with_iss_correct", "broaden ISS fixtures beyond the focused identity-band case"),
    Capability("--identity --tile --parallel", "supported-narrow", "checked identity tiling boundary composed with extracted checked one-coordinate parallel codegen over the validated polyhedral program", "pluto-compat identity-tiled-parallel; Opt_parallel_current_identity_tiled_result_correct; checked_tiling_validate plus checked_annotated_codegen", "broaden fixtures"),
    Capability("--identity --tile --parallel --multipar", "supported-narrow", "same checked identity tiling boundary, then extracted multi-cert parallel codegen for all distinct accepted schedule coordinates from Pluto hints", "pluto-compat identity-tiled-multipar; pluto-compat parallel-multipar-three-dims; Opt_parallel_current_many_identity_tiled_correct; checked_annotated_codegen_many", "broaden multipar fixtures; strict-mode hint-only positive checks are covered"),
    Capability("tile.sizes / --tile-sizes-file FILE", "supported-legacy-and-explicit-control-file", "Pluto reads this old working-directory file to choose tile sizes; PolOpt can now install it explicitly for the oracle call and accepts it because the checked tiling route validates the produced tile-size witness", "pluto-compat optimizer-implicit-tile-sizes-file; optimizer-explicit-tile-sizes-file; optimizer-explicit-tile-sizes-file-nodep; explicit-file cleanup check", "keep explicit option as preferred command-line interface"),
    Capability(".fst / --fusion-structure FILE", "supported-legacy-and-explicit-control-file", "Pluto reads this old working-directory file to force a fusion/distribution partition; PolOpt can now install it explicitly for the oracle call and accepts schedules that pass the checked affine validator", "pluto-compat optimizer-implicit-fst-file; optimizer-explicit-fst-file; optimizer-explicit-fst-file-fusion2; explicit-file cleanup check", "keep explicit option as preferred command-line interface"),
    Capability(".precut / --precut-file FILE", "supported-legacy-and-explicit-control-file", "Pluto reads this old working-directory file as a partial transformation to complete; PolOpt can now install it explicitly for the oracle call and accepts produced schedules that pass checked affine and tiling validators", "pluto-compat optimizer-implicit-precut-file; optimizer-explicit-precut-file; optimizer-explicit-precut-file-fusion2; explicit-file cleanup check", "keep explicit option as preferred command-line interface"),
    Capability("--iss", "supported", "ISS split validation composed with tiled, affine no-tiling, identity-tiled, parallel, vector, and diamond routes", "ISS suites; pluto-compat ordinary-tiled-iss and sequential-iss-notile; Opt_with_iss_correct", "keep route-specific acceptance checks"),
    Capability("--second-level-tile", "supported", "checked second-level tiling route, including ISS, explicit schedule-coordinate, and Pluto-hinted parallel compositions", "second-level suite; pluto-compat second-level-iss; pluto-compat second-level-parallel; pluto-compat second-level-parallel-matmul-init", "broaden fixtures"),
    Capability("--intratileopt", "supported", "typed tiled route with a separately checked final affine rescheduling inside tiles; rectangular and diamond producers use the same affine, tiling, affine theorem composition", "pluto-compat intratile matrix and native scheduled-OpenScop route checks; RawPostTilingAffine/RawPostTilingAffineISS generic post-tiling affine composition", "keep fail-closed validation and broaden inputs whose Pluto candidates exercise distinct intra-tile orders"),
    Capability("--parallel", "supported-component-verified", "Pluto-hinted route uses extracted tiling/parallel validators and codegen, with Pluto used only to choose candidate generated schedule coordinates", "pluto-compat parallel; pluto-compat parallel-multipar; compile_verified_correct; Opt_parallel_current_many_correct", "broaden hint-selection fixtures"),
    Capability("--parallel-current d", "supported", "legacy-named explicit option selecting canonical padded schedule coordinate d; native --identity-tiled --parallel-current d exposes the corresponding identity-tiling theorem route", "parallel-current suite; identity-tiled-current-combined-effect; Opt_parallel_current_correct; Opt_parallel_current_identity_tiled_result_correct", "keep the legacy spelling for compatibility and document its schedule-coordinate meaning"),
    Capability("--prevector / --vector", "supported-component-verified", "Pluto vector hints are parsed from OpenScop loop directive bit 4; statement scope disambiguates the generated-nest depth, which is then checked globally with the parallel/doall certificate and annotated only when every vector loop is structurally innermost", "pluto-compat prevector and default-prevector; checked_vector_annotated_codegen_correct_general; vector-current suite", "add statement-selective annotation or specialized semantics only for future outer-loop SIMD, reductions, fixed-width lanes, or backend-specific pragmas"),
    Capability("--vector-current d", "supported", "legacy-named explicit checked schedule coordinate; requires both the parallel/doall certificate and the innermost-only output gate", "vector-current suite; checked_vector_annotated_codegen_correct_general", "keep the legacy spelling for compatibility"),
    Capability("--const-unroll", "supported-sequential-and-parallel-seq-bodies", "independent extracted postpass that fully expands loops whose lower and upper bounds are integer constants, then applies verified cleanup; on annotated parallel output it transforms only sequential loops and preserves parallel/vector annotations and origin metadata", "pluto-compat native-const-unroll-constant-range and native-const-unroll-inside-parallel-current; end-to-end-c const_unroll and parallel_const_unroll; LoopUnroll.const_unroll_correct; extracted_sequential_compile_with_postpass_correct; extracted_parallel_compile_with_const_unroll_correct", "keep separate from --unrolljam; vector-route combinations remain rejected"),
    Capability("--unrolljam", "supported-narrow", "the extracted sequential endpoint composes optional constant unrolling, block/remainder unrolling, actual-domain cross-body validation, recursive checked jam lowering, and cleanup; parallel combinations are demonstrated by running the checked Loop postpass first and obtaining a fresh identity-codegen parallel certificate afterward; vector combinations and parallel reannotation of symbolic floor-division bounds remain rejected", "pluto-compat const-unrolljam-constant-loop; block-unrolljam-ufactor-variable-loop; mixed-const-and-block-unrolljam; parallel-unrolljam-constant-range; reject-parallel-unrolljam-symbolic-reannotation; unrolljam-context-bound-escape-rejected; LoopJamBridge.checked_pair_refines_sound; extracted_sequential_compile_with_unrolljam_correct; extracted_parallel_after_unrolljam_correct", "broaden parallel reannotation only when the Loop extractor supports the postpass result; do not claim general annotated-loop certificate transport"),
    Capability(".loop literal stride range(lb, ub, step)", "supported", "front-end syntax accepts nonzero integer literal strides and calls extracted LoopStride lowering; positive and negative directions both keep the extractor-facing Loop affine by using a unit-stride candidate loop plus affine guard, and checked codegen can recover the compact stride-indexed shape with theorem-backed symbolic expression display cleanup", "pluto-compat stride-loop-positive-literal; pluto-compat stride-loop-negative-literal; reject-stride-zero; reject-stride-symbolic; end-to-end-c stride_even; end-to-end-c stride_down; LoopStride.stride_loop_stmt_semantics; LoopStride.down_stride_loop_stmt_semantics; SLoopSymbolicSimpl.display_instr_expr_correct", "extend beyond literal strides only after adding a way to prove/enforce step sign and nonzero-ness"),
    Capability("--diamond-tile", "supported-narrow", "extracted four-phase diamond route with sequential, ISS, second-level, parallel, and multipar compositions", "diamond suite; pluto-compat diamond combinations; Opt_post_tiling_affine_band_correct", "broaden effect fixtures"),
    Capability("--full-diamond-tile", "supported-narrow", "stronger producer mode over the same extracted checked diamond route", "pluto-compat full-diamond; pluto-compat full-diamond-batch; Opt_post_tiling_affine_band_correct", "add more effect-distinguishing full-diamond cases"),
    Capability("--diamond-tile --iss", "supported-narrow", "ISS bridge validation is composed before the single-level four-phase diamond route", "pluto-compat diamond-iss; Opt_post_tiling_affine_band_with_iss_correct", "add broader ISS+diamond fixtures"),
    Capability("--full-diamond-tile --iss", "supported-narrow", "full-diamond producer mode over the same checked ISS+diamond route", "pluto-compat full-diamond-iss; Opt_post_tiling_affine_band_with_iss_correct", "add broader ISS+full-diamond fixtures"),
    Capability("--diamond-tile --second-level-tile", "supported-narrow", "second-level Pluto diamond output is checked by the same diamond route with second-level witness extraction enabled", "pluto-compat diamond-second-level; Opt_post_tiling_affine_band_correct", "add broader second-level diamond fixtures"),
    Capability("--diamond-tile --iss --second-level-tile", "supported-narrow", "ISS bridge validation composes with second-level diamond witness extraction", "pluto-compat diamond-iss-second-level; Opt_post_tiling_affine_band_with_iss_correct", "add broader ISS+second-level diamond fixtures"),
    Capability("--diamond-tile --parallel", "supported-narrow", "Pluto supplies the parallel hint; polopt validates the selected schedule coordinate, returns metadata-preserving cleaned code when every proof-stage trace is affine, and otherwise falls back to the checked standard raw form", "pluto-compat diamond-parallel; pluto-compat diamond-parallel-jacobi-batch; Opt_parallel_current_post_tiling_affine_correct", "broaden cleaned and raw-fallback fixtures"),
    Capability("--diamond-tile --parallel --multipar", "supported-narrow", "the extracted diamond pipeline can feed a list of candidate schedule coordinates into the checked multi-cert parallel codegen route", "pluto-compat diamond-parallel-multipar; Opt_parallel_current_many_post_tiling_affine_correct; checked_annotated_codegen_many_correct_general", "broaden diamond multipar fixtures; strict-mode hint-only positive checks are covered"),
    Capability("--diamond-tile --iss --parallel", "supported-narrow", "ISS bridge validation composes with the Pluto-hinted diamond parallel-current route", "pluto-compat diamond-iss-parallel; Opt_parallel_current_post_tiling_affine_with_iss_correct", "broaden ISS fixtures beyond the single-statement batch stencil"),
    Capability("--diamond-tile --iss --parallel --multipar", "supported-narrow", "ISS bridge validation composes with the Pluto-hinted diamond multi-cert parallel-current route", "pluto-compat diamond-iss-parallel-multipar; Opt_parallel_current_many_post_tiling_affine_with_iss_correct; checked_annotated_codegen_many_correct_general", "broaden ISS diamond multipar fixtures; strict-mode hint-only positive checks are covered"),
    Capability("--diamond-tile --parallel-current d", "supported-narrow", "diamond route validates the four-phase boundary before explicit schedule-coordinate parallel certification; positive support includes cleaned single-statement output and the checked raw fallback for batched Jacobi", "parallel-current diamond-current-combined-effect; parallel-current diamond-current-jacobi-batch-positive; Opt_parallel_current_post_tiling_affine_correct", "broaden explicit-coordinate fixtures"),
    Capability("--candldep --scalpriv", "supported-conservative-oracle-tuning", "Candl scalar-privatization is passed to Pluto only with --candldep; PolOpt still validates the produced schedule and parallel hints under the original scalar storage semantics", "pluto-compat optimizer-candldep-scalpriv-affine; optimizer-candldep-scalpriv-parallel-conservative; bare --scalpriv rejection", "add a checked scalar-private storage rewrite before accepting schedules or parallel hints that require privatization"),
]

DIAMOND_COMBINATIONS = [
    Capability("--diamond-tile --notile", "correct-rejection", "diamond requires a tiling phase", "route rejection", "keep rejecting"),
    Capability("--diamond-tile --identity", "correct-rejection", "diamond requires Pluto scheduling/skew plus tiling", "route rejection", "keep rejecting unless a meaningful identity-diamond route is designed"),
    Capability("--identity --tile --diamond-tile", "correct-rejection", "direct Pluto's identity diamond output is not distinct from ordinary identity tiling on the 63-fixture regression corpus; the focused wavefront phase dump validates but exposes no route-specific output effect", "tools/regression/explore_identity_compositions.py; compat rejection", "keep rejecting unless a distinct identity-diamond effect fixture appears"),
]


def table_rows() -> list[Capability]:
    rows: list[Capability] = []
    rows.extend(SUPPORTED)
    rows.extend(DIAMOND_COMBINATIONS)
    for flag, reason in sorted(compat.SUPPORTED_OPTIMIZER_OPTIONS.items()):
        if flag == "--intratileopt":
            continue
        rows.append(Capability(flag, "supported-oracle-tuning", reason, "pluto-compat optimizer tuning checks; existing affine/tiling validators re-check the produced schedule", "broaden fixtures for additional effect cases"))
    for flag, reason in sorted(compat.SUPPORTED_VALUE_OPTIONS.items()):
        rows.append(Capability(flag + " <n>", "supported-oracle-tuning", reason, "pluto-compat optimizer tuning checks; existing affine/tiling validators re-check the produced schedule", "broaden value/effect fixtures"))
    for flag, reason in sorted(compat.CONDITIONAL_LP_SOLVER_OPTIONS.items()):
        rows.append(Capability(flag, "supported-oracle-tuning-with-runtime-probe", reason, "pinned GLPK-enabled Pluto baseline accepts and validates representative affine cases, including non-matmul DFP/typed/hybrid/delayedcut checks where applicable; alternate Pluto binaries are rejected if they lack the advertised option", "broaden delayed-cut-specific and non-dense-kernel effect fixtures"))

    for flag, reason in sorted(compat.FRONTEND_OPTIONS.items()):
        rows.append(Capability(flag, "out-of-optimizer-surface", reason, "native compat rejection", "keep as separate importer/debug mode if needed"))
    for flag, reason in sorted(compat.CODEGEN_OPTIONS.items()):
        evidence = "native compat rejection"
        if flag == "--unrolljam":
            evidence = "native compat rejection; codegen-gap exploration shows unchanged after-scheduling scop but changed generated C"
        rows.append(Capability(flag, "validator-or-codegen-gap", reason, evidence, "implement checked PolOpt equivalent, not Pluto pass-through"))
    for flag, reason in sorted(compat.DFP_OPTIONS.items()):
        rows.append(Capability(flag, "surface-or-build-gap", reason, "native compat rejection", "enable solver build and validate produced affine schedules"))
    for flag, reason in sorted(compat.UNSUPPORTED_OPTIMIZER_OPTIONS.items()):
        rows.append(Capability(flag, "surface-gap", reason, "native compat rejection", "pass through as oracle tuning only after regression coverage"))
    for flag, reason in sorted(compat.DEPENDENCE_SOLVER_OPTIONS.items()):
        rows.append(Capability(flag, "validator-or-semantic-gap", reason, "native compat rejection", "implement a checked PolOpt equivalent before pass-through"))
    for flag, reason in sorted(compat.STALE_OR_NON_PLUTO_OPTIONS.items()):
        rows.append(Capability(flag, "stale-or-non-pluto", reason, "native compat stale/current-Pluto rejection checks", "do not expose as optimizer compatibility"))
    return rows


def check_rows() -> list[dict[str, object]]:
    rows = []
    for check in compat_suite.active_checks():
        rows.append(
            {
                "name": check.name,
                "args": check.args,
                "expect": "success" if check.success else "reject",
                "needle": check.needle,
                "normalized": check.normalized,
                "effect_needles": list(check.effect_needles),
                "effect_absent": list(check.effect_absent),
                "scheduled_needles": list(check.scheduled_needles),
                "scheduled_absent": list(check.scheduled_absent),
                "differs_from_args": [list(args) for args in check.differs_from_args],
                "same_as_args": list(check.same_as_args) if check.same_as_args is not None else None,
                "implicit_control_file": check.implicit_control_file,
                "implicit_control_file_content": check.implicit_control_file_content,
                "explicit_control_flag": check.explicit_control_flag,
                "fixture": str(check.fixture.relative_to(ROOT)),
            }
        )
    return rows


def build_matrix() -> dict[str, object]:
    return {
        "root": str(ROOT),
        "capabilities": [asdict(row) for row in table_rows()],
        "compatibility_checks": check_rows(),
        "summary": {
            "capability_rows": len(table_rows()),
            "compatibility_checks": len(compat_suite.active_checks()),
            "diamond_supported_route": "sequential, parallel, multipar, ISS, and second-level four-phase routes",
            "pluto_style_entry": "./polopt --pluto-compat",
            "remaining_semantic_gaps": [
                {
                    "request": "symbolic or runtime-dependent stride steps",
                    "reason": "The supported front-end stride form requires a nonzero integer literal. This keeps the lowered candidate domain affine and avoids adding a runtime proof obligation for the step sign and nonzero-ness.",
                    "required_work": "Add a sign/nonzero certificate or checked precondition for affine/dynamic step expressions, then reuse the LoopStride affine-guard lowering under that certificate.",
                },
                {
                    "request": "full --candldep --scalpriv",
                    "reason": "Current support is conservative oracle tuning; schedules that rely on privatized scalar instances need a checked storage rewrite.",
                    "required_work": "Materialize private scalar storage or an equivalent loop-local representation and prove preservation under the scalar-privatization precondition.",
                },
            ],
        },
    }


def write_markdown(matrix: dict[str, object]) -> str:
    lines = [
        "# Pluto/PolOpt Capability Matrix",
        "",
        "- Pluto-style filtered entry: `./polopt --pluto-compat`",
        "",
        "## Capability Surface",
        "",
        "| Request | Status | Reason | Evidence | Next step |",
        "|---|---|---|---|---|",
    ]
    for row in matrix["capabilities"]:  # type: ignore[index]
        lines.append(
            f"| `{row['request']}` | {row['status']} | {row['reason']} | {row['evidence']} | {row['next_step']} |"
        )
    lines.extend([
        "",
        "## Remaining Semantic Gaps",
        "",
        "| Request | Reason | Required work |",
        "|---|---|---|",
    ])
    for gap in matrix["summary"]["remaining_semantic_gaps"]:  # type: ignore[index]
        lines.append(
            f"| `{gap['request']}` | {gap['reason']} | {gap['required_work']} |"
        )
    lines.extend(["", "## Compatibility Checks", "", "| Check | Expectation | Fixture | Args | Effect oracle |", "|---|---|---|---|---|"])
    for row in matrix["compatibility_checks"]:  # type: ignore[index]
        args = " ".join(row["args"])
        effect_parts = []
        if row["effect_needles"]:
            effect_parts.append("requires " + ", ".join(f"`{needle}`" for needle in row["effect_needles"]))
        if row["effect_absent"]:
            effect_parts.append("forbids " + ", ".join(f"`{needle}`" for needle in row["effect_absent"]))
        if row["scheduled_needles"]:
            effect_parts.append("scheduled OpenScop requires " + ", ".join(f"`{needle}`" for needle in row["scheduled_needles"]))
        if row["scheduled_absent"]:
            effect_parts.append("scheduled OpenScop forbids " + ", ".join(f"`{needle}`" for needle in row["scheduled_absent"]))
        if row["differs_from_args"]:
            effect_parts.append("differs from baseline")
        if row["same_as_args"] is not None:
            effect_parts.append("matches baseline")
        effect = "; ".join(effect_parts) if effect_parts else ""
        if row["implicit_control_file"]:
            effect = (effect + "; " if effect else "") + f"with `{row['implicit_control_file']}` present"
        if row["explicit_control_flag"]:
            effect = (effect + "; " if effect else "") + f"with `{row['explicit_control_flag']}` file"
        lines.append(f"| `{row['name']}` | {row['expect']} | `{row['fixture']}` | `{args}` | {effect} |")
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json-out")
    ap.add_argument("--markdown-out")
    args = ap.parse_args()

    matrix = build_matrix()
    if args.json_out:
        out = Path(args.json_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(matrix, indent=2, sort_keys=True))
    if args.markdown_out:
        out = Path(args.markdown_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(write_markdown(matrix))
    if not args.json_out and not args.markdown_out:
        print(write_markdown(matrix), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
