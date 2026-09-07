#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.ci.check_open_proofs import find_open_proofs

SCAN_DIRS = [
    "src",
    "driver",
    "polygen",
    "syntax",
    "common",
    "cfrontend",
    "cparser",
    "lib",
    "VPL/coq",
]

TOP_LEVEL_ROUTES = [
    {
        "route": "default band-aware sequential optimizer",
        "cli": "polopt <file.loop>",
        "theorem_file": "driver/PolOptBandTiling.v",
        "theorem_names": ["Opt_band_correct", "Opt_prepared_band_correct"],
    },
    {
        "route": "unified direct-only permutable-band tiling dispatcher",
        "cli": "every ordinary, second-level, identity-tiled, ISS, diamond, parallel, vector, and multipar tiling boundary",
        "theorem_file": "src/TilingBandDirectRuntime.v",
        "theorem_names": [
            "checked_second_level_direct_band_check_correct",
            "checked_tiling_sourceb_first_direct_band_check_correct",
            "checked_tiling_sourceb_complete_direct_band_check_sourceb_true",
            "checked_tiling_sourceb_complete_direct_band_check_correct",
            "checked_tiling_sourceb_complete_direct_band_check_outer_correct",
            "checked_tiling_schedule_sourceb_first_direct_runtime_validate_route_correct",
        ],
        "note": "The executable dispatcher accepts supported ordinary, identity, mixed-depth, diamond, and second-level tilings only through proved semantic permutable-band checks; malformed or unsupported layouts are rejected rather than passed to another tiling validator.",
    },
    {
        "route": "direct semantic permutable-band checker",
        "cli": "internal primary tiling validator for recognized common-band and componentwise second-level layouts",
        "theorem_file": "src/TilingBandScheduleValidator.v",
        "theorem_names": [
            "validate_two_instrs_pluto_band_component_direct_sound",
            "check_pinstr_list_pluto_permutable_band_direct_sound",
            "check_pprog_pluto_permutable_tiling_bands_direct_sound_with_env_len",
            "check_pinstr_list_pluto_componentwise_permutable_bands_direct_sound",
            "ordinary_semantic_band_shape_reversal_bridge",
            "second_level_semantic_band_shape_reversal_bridge",
            "checked_tiling_sourceb_semantic_band_direct_correct_same_ctxt",
        ],
        "note": "This is a sound semantic analogue of Pluto's fully permutable-band condition. It does not claim to verify Pluto's dependence-graph construction, band search, or detector implementation.",
    },
    {
        "route": "phase-separated ordinary direct checker",
        "cli": "internal direct branch for ordinary strip mining with statement-specific band widths after unique constant phase rows",
        "theorem_file": "src/TilingBandMixedSecondValidator.v",
        "theorem_names": [
            "phase_separated_ordinary_reversal_same_class",
            "phase_class_ordinary_local_reversal_bridge_wf_with_env_len",
            "check_pprog_phase_separated_ordinary_direct_true_inv",
            "check_pprog_phase_separated_ordinary_direct_correct_same_ctxt",
        ],
        "note": "The branch preserves each leading phase row, uses phase uniqueness to exclude cross-statement reversals, and checks each statement's inferred band with the direct componentwise permutable-band checker.",
    },
    {
        "route": "phase-aware mixed second-level direct checker",
        "cli": "internal direct branch for the recognized grouped mixed-depth second-level layout",
        "theorem_file": "src/TilingBandMixedSecondValidator.v",
        "theorem_names": [
            "mixed_second_level_local_reversal_bridge_wf_with_env_len",
            "check_pprog_mixed_second_level_direct_true_inv",
            "check_pprog_mixed_second_level_direct_correct_same_ctxt",
        ],
        "note": "This fail-closed branch requires grouped schedules, band start one, and globally unique constant phase rows. It proves soundness for the recognized class, not completeness for every mixed second-level tiling.",
    },
    {
        "route": "identity extraction/codegen route",
        "cli": "polopt --identity --notile <file.loop>",
        "theorem_file": "driver/PolOptCorrect.v",
        "theorem_names": ["Identity_opt_prepared_correct"],
    },
    {
        "route": "band-first identity second-level tiling route",
        "cli": "polopt --identity-tiled --second-level-tile <file.loop>",
        "theorem_file": "driver/PolOptBandTiling.v",
        "theorem_names": [
            "Opt_prepared_identity_tiled_band_correct",
            "Opt_identity_tiled_band_correct",
        ],
    },
    {
        "route": "checked ISS plus band-first identity second-level tiling route",
        "cli": "polopt --iss --identity-tiled --second-level-tile <file.loop>",
        "theorem_file": "driver/PolOptBandTiling.v",
        "theorem_names": [
            "Opt_prepared_identity_tiled_band_with_iss_correct",
            "Opt_identity_tiled_band_with_iss_correct",
        ],
    },
    {
        "route": "affine-only route",
        "cli": "polopt --notile <file.loop>",
        "theorem_file": "driver/PolOptCorrect.v",
        "theorem_names": ["Affine_opt_prepared_correct"],
    },
    {
        "route": "legacy CLI alias for band-first sequential optimizer",
        "cli": "polopt --legacy-generic-tiling <file.loop>",
        "theorem_file": "driver/PolOptBandTiling.v",
        "theorem_names": ["Opt_band_correct", "Opt_prepared_band_correct"],
    },
    {
        "route": "band-first ISS optimizer",
        "cli": "polopt --iss <file.loop>",
        "theorem_file": "driver/PolOptBandTiling.v",
        "theorem_names": ["Opt_band_with_iss_correct", "Opt_prepared_band_with_iss_correct"],
    },
    {
        "route": "checked parallel current",
        "cli": "polopt --parallel-current <dim> <file.loop>",
        "theorem_file": "driver/ParallelPolOptCorrect.v",
        "theorem_names": ["Opt_parallel_current_correct"],
    },
    {
        "route": "checked raw parallel codegen form",
        "cli": "internal checked alternative used by parallel-current routes",
        "theorem_file": "src/ParallelCodegenCorrect.v",
        "theorem_names": ["checked_annotated_codegen_correct_general"],
        "note": "The selector returns metadata-preserving cleaned output only when every proof-relevant cleanup stage passes the executable trace-safety gate; otherwise it retains the checked standard-raw singleton-loop output.",
    },
    {
        "route": "raw parallel codegen compatibility endpoint",
        "cli": "internal generic endpoint retained for compatibility consumers",
        "theorem_file": "src/ParallelCodegenCompatibility.v",
        "theorem_names": ["annotated_codegen_raw_correct_general"],
        "note": "This compatibility theorem exposes the raw generated-program endpoint; certificate-backed compiler routes use the checked theorem above.",
    },
    {
        "route": "raw prepared codegen",
        "cli": "internal codegen before singleton cleanup",
        "theorem_file": "src/PrepareCodegen.v",
        "theorem_names": [
            "prepared_codegen_raw_correct",
            "prepared_codegen_raw_correct_general",
        ],
    },
    {
        "route": "checked post-tiling affine plus parallel current",
        "cli": "polopt --diamond-tile --parallel-current <dim> <file.loop>",
        "theorem_file": "driver/ParallelPolOptCorrect.v",
        "theorem_names": [
            "Opt_parallel_current_post_tiling_affine_correct",
            "Opt_parallel_current_post_tiling_affine_result_correct",
            "parallel_current_post_tiling_affine_prepared_from_poly_correct",
        ],
    },
    {
        "route": "verified constant-unroll compiler postpass",
        "cli": "polopt --const-unroll <file.loop>",
        "theorem_file": "driver/ExtractedPipelineCorrect.v",
        "theorem_names": ["extracted_sequential_compile_with_postpass_correct"],
        "note": "The extracted endpoint composes the selected sequential producer theorem with constant-bound unrolling and cleanup.",
    },
    {
        "route": "verified sequential unroll-jam compiler endpoint",
        "cli": "polopt --pluto-compat --unrolljam [--ufactor N] <file.loop>",
        "theorem_file": "driver/ExtractedPipelineCorrect.v",
        "theorem_names": ["extracted_sequential_compile_with_unrolljam_correct"],
        "note": "The theorem composes the selected producer with optional constant unrolling, checked block/remainder unroll-jam, and cleanup. The candidate selector is universally quantified.",
    },
    {
        "route": "checked unroll-jam followed by fresh parallel validation",
        "cli": "polopt --pluto-compat --unrolljam --parallel [--multipar] <file.loop>",
        "theorem_file": "driver/ExtractedPipelineCorrect.v",
        "theorem_names": [
            "extracted_parallel_after_unrolljam_correct",
            "extracted_parallel_many_after_unrolljam_correct",
        ],
        "note": "These theorems compose the checked sequential postpass with fresh identity-route extraction and parallel certification. They do not transport annotations through arbitrary transformed Loop nests.",
    },
    {
        "route": "loop-native same-bound sibling jam theorem",
        "cli": "internal building block used by locally validated --unrolljam fusion",
        "theorem_file": "src/LoopJamNative.v",
        "theorem_names": ["jammed_two_loop_instance_refines_unjammed"],
        "note": "The theorem proves that a jammed same-range sibling-loop instance list refines the original unjammed sibling loops under the trace cross-permutability certificate.",
    },
    {
        "route": "single same-bound sibling-loop jam refinement",
        "cli": "semantic building block for the extracted jam lowerer",
        "theorem_file": "src/LoopJamLower.v",
        "theorem_names": ["try_jam_pair_exact_sound"],
        "note": "This theorem is the native single-pair semantic component. LoopJamBridge supplies its trace premise from the extracted affine certificate, and LoopJamContext lifts accepted pairs through recursive lowering contexts.",
    },
    {
        "route": "per-candidate sibling-loop jam validator",
        "cli": "internal validator called by extracted --unrolljam lowerer for each same-bound sibling-loop candidate",
        "theorem_file": "src/LoopJamValidator.v",
        "theorem_names": ["checked_loop_jam_pair_at_depth_pointwise_sound"],
        "note": "The validator retains equal parameter/enclosing-iterator schedule coordinates and reverses the body-group row to certify cross-body independence inside each shared outer environment over the candidate's actual bounds.",
    },
    {
        "route": "checked sibling-loop jam certificate bridge",
        "cli": "proof component used by the extracted --unrolljam lowerer",
        "theorem_file": "src/LoopJamBridge.v",
        "theorem_names": ["checked_pair_refines_sound"],
        "note": "The bridge transports the pointwise affine certificate to native trace permutability and closes both ordinary and guarded checked-pair refinement.",
    },
    {
        "route": "verified Loop cleanup post pass",
        "cli": "internal post pass used after checked unroll",
        "theorem_file": "polygen/LoopSingletonCleanup.v",
        "theorem_names": ["cleanup_correct"],
    },
    {
        "route": "positive-literal stride range lowering",
        "cli": "front-end lowering for .loop syntax range(lb, ub, step) where step is a positive integer literal",
        "theorem_file": "polygen/LoopStride.v",
        "theorem_names": ["stride_loop_stmt_semantics"],
        "note": "The extracted front end lowers stride loops to an affine over-approximation plus affine guard, so the verified extractor still sees an affine SCoP and codegen can recover the compact ceil-divided loop bound.",
    },
    {
        "route": "negative-literal stride range lowering",
        "cli": "front-end lowering for .loop syntax range(lb, ub, step) where step is a negative integer literal",
        "theorem_file": "polygen/LoopStride.v",
        "theorem_names": ["down_stride_loop_stmt_semantics"],
        "note": "The extracted front end mirrors the positive-stride route by using a unit candidate loop, the affine iterator lb - step*k, and the affine guard ub + 1 <= iterator.",
    },
    {
        "route": "verified symbolic expression display simplification",
        "cli": "internal post-output simplifier used by .loop pretty printing",
        "theorem_file": "syntax/SLoopSymbolicSimpl.v",
        "theorem_names": ["display_affine_expr_correct", "display_instr_expr_correct"],
        "note": "The extracted pretty path lowers pure integer instruction expressions through the current Loop slots, simplifies the resulting Loop expression, and prints that theorem-backed expression instead of the raw slot-expanded syntax.",
    },
    {
        "route": "enumerated verified compiler config wrapper",
        "cli": "internal compiler wrapper: check_config followed by compile_verified",
        "theorem_file": "driver/VerifiedCompilerConfig.v",
        "theorem_names": [
            "compile_correct",
            "compile_verified_correct",
            "compile_unsupported_no_result",
        ],
        "note": "This proof-side wrapper states correctness for the abstract route definitions used by the extracted configuration.",
    },
    {
        "route": "exact extracted compiler dispatcher bridge",
        "cli": "all sequential, parallel-current, vector-current, and multipar configurations selected by polopt",
        "theorem_file": "driver/ExtractedPipelineCorrect.v",
        "theorem_names": [
            "extracted_sequential_compile_verified_correct",
            "extracted_sequential_compile_correct",
            "extracted_parallel_compile_verified_correct",
            "extracted_parallel_compile_correct",
        ],
        "note": "These theorems prove the concrete syntax/SVerified* configurations used by extraction, branch by branch, via explicit equality bridges to the proof-side optimizer modules.",
    },
    {
        "route": "unified Loop-to-ParallelLoop compiler config wrapper",
        "cli": "normal polopt sequential route, explicit --parallel-current route, and Pluto-hinted --parallel/--multipar routes",
        "theorem_file": "driver/VerifiedParallelCompilerConfig.v",
        "theorem_names": [
            "compile_correct",
            "compile_verified_correct",
            "compile_seq_verified_correct",
            "checked_sequential_current_annotated_codegen_correct",
            "compile_unsupported_no_result",
        ],
        "note": "This wrapper gives a single Loop -> ParallelLoop end-to-end theorem. Sequential routes use checked all-SeqMode ParallelLoop codegen. Parallel routes certify padded schedule coordinates, derive ordering for each actual target execution, and use cleaned output only when every proof-relevant cleanup stage is trace-safe; otherwise they retain the checked standard-raw form. Pluto-hinted --parallel and --multipar are candidate-selection layers over the same checked compiler; --multipar dispatches through RawParallelCurrentMany* configs and the extracted Coq route filters the candidate list to all certifiable coordinates before checked multi-cert codegen. The underlying route theorems live in driver/ParallelPolOptCorrect.v, including Opt_parallel_current_many_correct, Opt_parallel_current_many_identity_tiled_correct, and Opt_parallel_current_many_post_tiling_affine_correct.",
    },
    {
        "route": "checked ISS plus post-tiling affine plus parallel current",
        "cli": "polopt --iss --diamond-tile --parallel-current <dim> <file.loop>",
        "theorem_file": "driver/ParallelPolOptCorrect.v",
        "theorem_names": [
            "Opt_parallel_current_post_tiling_affine_with_iss_correct",
            "Opt_parallel_current_post_tiling_affine_with_iss_result_correct",
            "parallel_current_post_tiling_affine_prepared_from_poly_with_iss_correct",
        ],
    },
    {
        "route": "post-tiling affine optimizer",
        "cli": "polopt --diamond-tile <file.loop>",
        "theorem_file": "driver/PolOptBandTiling.v",
        "theorem_names": [
            "Opt_post_tiling_affine_band_correct",
            "Opt_prepared_post_tiling_affine_band_correct",
            "try_post_tiling_affine_phase_pipeline_from_source_pol_band_correct",
        ],
        "note": "Also covers --full-diamond-tile and --second-level-tile through the same extracted route.",
    },
    {
        "route": "ISS plus post-tiling affine optimizer",
        "cli": "polopt --iss --diamond-tile <file.loop>",
        "theorem_file": "driver/PolOptBandTiling.v",
        "theorem_names": [
            "Opt_post_tiling_affine_band_with_iss_correct",
            "Opt_prepared_post_tiling_affine_band_with_iss_correct",
            "try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_band_correct",
        ],
        "note": "Also covers --iss --full-diamond-tile and --iss --second-level-tile through the same extracted route.",
    },
]


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    text: str


def iter_coq_files() -> list[Path]:
    files: list[Path] = []
    for rel in SCAN_DIRS:
        root = ROOT / rel
        if not root.exists():
            continue
        files.extend(sorted(root.rglob("*.v")))
    return files


def scan_open_proofs(files: list[Path]) -> tuple[list[Finding], list[Finding]]:
    admitted: list[Finding] = []
    aborted: list[Finding] = []
    for path in files:
        try:
            lines = path.read_text(errors="replace").splitlines()
            markers = find_open_proofs(path)
        except OSError:
            continue
        rel = str(path.relative_to(ROOT))
        for line, marker in markers:
            finding = Finding(rel, line, lines[line - 1].strip())
            if marker.startswith("Abort"):
                aborted.append(finding)
            else:
                admitted.append(finding)
    return admitted, aborted


def theorem_index(files: list[Path]) -> dict[str, list[str]]:
    pattern = re.compile(r"^\s*(Theorem|Lemma|Corollary|Proposition)\s+([A-Za-z0-9_']+)")
    index: dict[str, list[str]] = {}
    for path in files:
        rel = str(path.relative_to(ROOT))
        names: list[str] = []
        try:
            lines = path.read_text(errors="replace").splitlines()
        except OSError:
            continue
        for line in lines:
            match = pattern.match(line)
            if match:
                names.append(match.group(2))
        if names:
            index[rel] = names
    return index


def build_report() -> dict[str, object]:
    files = iter_coq_files()
    admitted, aborted = scan_open_proofs(files)
    extraction_axioms = []
    extraction_dir = ROOT / "extraction"
    if extraction_dir.exists():
        for path in sorted(extraction_dir.glob("*.ml")):
            for idx, line in enumerate(path.read_text(errors="replace").splitlines(), start=1):
                if "AXIOM TO BE REALIZED" in line:
                    extraction_axioms.append(Finding(str(path.relative_to(ROOT)), idx, line.strip()))

    index = theorem_index(files)
    flat_theorems = {
        (path, name)
        for path, names in index.items()
        for name in names
    }
    missing_route_theorems = []
    for route in TOP_LEVEL_ROUTES:
        theorem_file = route["theorem_file"]
        for name in route.get("theorem_names", []):
            if name == "band-aware tiling validator lemmas":
                continue
            if (theorem_file, name) not in flat_theorems:
                missing_route_theorems.append(
                    {
                        "route": route["route"],
                        "theorem_file": theorem_file,
                        "theorem_name": name,
                    }
                )

    return {
        "root": str(ROOT),
        "scanned_dirs": SCAN_DIRS,
        "coq_file_count": len(files),
        "admitted_count": len(admitted),
        "abort_count": len(aborted),
        "extraction_axiom_count": len(extraction_axioms),
        "missing_route_theorem_count": len(missing_route_theorems),
        "admitted": [asdict(item) for item in admitted],
        "aborted": [asdict(item) for item in aborted],
        "extraction_axioms": [asdict(item) for item in extraction_axioms],
        "missing_route_theorems": missing_route_theorems,
        "top_level_routes": TOP_LEVEL_ROUTES,
        "theorem_index": index,
    }


def write_markdown(report: dict[str, object]) -> str:
    lines = [
        "# PolCert Proof Report",
        "",
        f"- Coq files scanned: `{report['coq_file_count']}`",
        f"- Local admitted markers: `{report['admitted_count']}`",
        f"- Local abort markers: `{report['abort_count']}`",
        f"- Extracted OCaml unrealized axioms: `{report['extraction_axiom_count']}`",
        f"- Missing listed route theorems: `{report['missing_route_theorem_count']}`",
        "",
        "## Route Map",
        "",
        "| Route | CLI | Theorem file | Theorem names | Note |",
        "|---|---|---|---|---|",
    ]
    for route in report["top_level_routes"]:  # type: ignore[index]
        item = route
        names = ", ".join(item.get("theorem_names", []))
        note = item.get("note", "")
        lines.append(
            f"| {item['route']} | `{item['cli']}` | `{item['theorem_file']}` | {names} | {note} |"
        )

    if report["admitted_count"] or report["abort_count"]:  # type: ignore[index]
        lines.extend(["", "## Open Proof Markers", ""])
        for key in ("admitted", "aborted"):
            for item in report[key]:  # type: ignore[index]
                lines.append(f"- `{item['path']}:{item['line']}`: `{item['text']}`")
    if report["missing_route_theorem_count"]:  # type: ignore[index]
        lines.extend(["", "## Missing Route Theorems", ""])
        for item in report["missing_route_theorems"]:  # type: ignore[index]
            lines.append(
                f"- `{item['theorem_file']}`: `{item['theorem_name']}` for {item['route']}"
            )
    return "\n".join(lines) + "\n"


def report_has_errors(report: dict[str, object]) -> bool:
    return bool(
        report["admitted_count"]
        or report["abort_count"]
        or report["extraction_axiom_count"]
        or report["missing_route_theorem_count"]
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json-out")
    ap.add_argument("--markdown-out")
    args = ap.parse_args()

    report = build_report()
    if args.json_out:
        out = Path(args.json_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(report, indent=2, sort_keys=True))
    if args.markdown_out:
        out = Path(args.markdown_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(write_markdown(report))
    if not args.json_out and not args.markdown_out:
        print(write_markdown(report), end="")
    else:
        result = "FAIL" if report_has_errors(report) else "PASS"
        print(
            f"[proof-report] {result} "
            "expected=admitted:0,aborted:0,extraction-axioms:0,missing-routes:0 "
            f"actual=admitted:{report['admitted_count']},"
            f"aborted:{report['abort_count']},"
            f"extraction-axioms:{report['extraction_axiom_count']},"
            f"missing-routes:{report['missing_route_theorem_count']} "
            "interpretation=proof sources and extracted routes are closed"
        )
    if report_has_errors(report):
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
