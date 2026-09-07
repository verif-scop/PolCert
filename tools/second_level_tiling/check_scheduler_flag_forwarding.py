#!/usr/bin/env python3
"""Static regression checks for second-level Pluto flag forwarding."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def definition_body(source: str, name: str) -> str:
    match = re.search(rf"^let {re.escape(name)}\b[^=]*=", source, re.MULTILINE)
    if match is None:
        raise AssertionError(f"missing Scheduler definition: {name}")
    next_definition = re.search(r"^let \w", source[match.end() :], re.MULTILINE)
    end = len(source) if next_definition is None else match.end() + next_definition.start()
    return source[match.end() : end]


def extracted_definition_body(source: str, name: str) -> str:
    match = re.search(
        rf"^(?P<indent>[ \t]*)let {re.escape(name)}\b[^=]*=",
        source,
        re.MULTILINE,
    )
    if match is None:
        raise AssertionError(f"missing extracted definition: {name}")
    indent = re.escape(match.group("indent"))
    next_definition = re.search(
        rf"^{indent}let \w",
        source[match.end() :],
        re.MULTILINE,
    )
    end = (
        len(source)
        if next_definition is None
        else match.end() + next_definition.start()
    )
    return source[match.end() : end]


def coq_definition_body(source: str, name: str) -> str:
    match = re.search(
        rf"^(?:Definition|Fixpoint) {re.escape(name)}\b[\s\S]*?:=",
        source,
        re.MULTILINE,
    )
    if match is None:
        raise AssertionError(f"missing Coq definition: {name}")
    next_item = re.search(
        r"^(?:Definition|Lemma|Theorem|Inductive|Fixpoint)\s",
        source[match.end() :],
        re.MULTILINE,
    )
    end = len(source) if next_item is None else match.end() + next_item.start()
    return source[match.end() : end]


def coq_inductive_constructors(source: str, name: str) -> list[str]:
    match = re.search(
        rf"^Inductive {re.escape(name)}\b[\s\S]*?:=(?P<body>[\s\S]*?)\.\s*$",
        source,
        re.MULTILINE,
    )
    if match is None:
        raise AssertionError(f"missing Coq inductive: {name}")
    return re.findall(r"^\|\s*([A-Za-z0-9_']+)", match.group("body"), re.MULTILINE)


def require(body: str, needle: str, route: str) -> None:
    if needle not in body:
        raise AssertionError(f"{route} does not forward {needle}")


def require_count(body: str, needle: str, count: int, route: str) -> None:
    actual = body.count(needle)
    if actual != count:
        raise AssertionError(
            f"{route} contains {actual} occurrences of {needle}, expected {count}"
        )


def main() -> None:
    scheduler = (ROOT / "driver" / "Scheduler.ml").read_text(encoding="utf-8")

    user_facing_recipes = (
        "affine_only_flags",
        "tile_only_flags",
        "affine_only_parallel_flags",
        "affine_only_vector_flags",
        "tile_only_parallel_flags",
        "tile_only_vector_flags",
        "post_tiling_affine_flags",
        "post_tiling_affine_parallel_flags",
        "post_tiling_affine_vector_flags",
    )
    for route in user_facing_recipes:
        if '"--rar"' in definition_body(scheduler, route):
            raise AssertionError(f"{route} enables non-default Pluto RAR relations")
    require(
        definition_body(scheduler, "invoke_pluto"),
        '"--rar"',
        "legacy 62-case evaluation recipe",
    )

    cli = (ROOT / "syntax" / "SLoopCli.ml").read_text(encoding="utf-8")
    require(cli, '| "--rar" ->', "explicit RAR CLI branch")
    require(cli, 'add_pluto_extra_flag cfg "--rar"', "explicit RAR forwarding")
    rar_branch = re.search(
        r'\| "--rar" ->(?P<body>[\s\S]*?)go \(i \+ 1\)',
        cli,
    )
    if rar_branch is None:
        raise AssertionError("could not isolate explicit RAR CLI branch")
    if "enable_pluto_compat cfg" in rar_branch.group("body"):
        raise AssertionError("--rar must remain composable with native checked routes")
    require(cli, '| "--innerpar" ->', "explicit innerpar CLI branch")
    require(cli, 'add_pluto_extra_flag cfg "--innerpar"', "explicit innerpar forwarding")

    for route in (
        "post_tiling_affine_flags",
        "post_tiling_affine_parallel_flags",
        "post_tiling_affine_vector_flags",
    ):
        require(
            definition_body(scheduler, route),
            "second_level_tiling_flags ()",
            route,
        )

    for route, base in (
        ("post_tiling_affine_with_iss_flags", "post_tiling_affine_flags ()"),
        (
            "post_tiling_affine_parallel_with_iss_flags",
            "post_tiling_affine_parallel_flags ()",
        ),
        ("post_tiling_affine_vector_with_iss_flags", "post_tiling_affine_vector_flags ()"),
    ):
        require(definition_body(scheduler, route), base, route)

    for route in (
        "tile_only_parallel_second_level_flags",
        "tile_only_vector_second_level_flags",
    ):
        require(definition_body(scheduler, route), '"--second-level-tile"', route)

    driver_config = (ROOT / "driver" / "VerifiedCompilerConfig.v").read_text(
        encoding="utf-8"
    )
    syntax_config = (ROOT / "syntax" / "SVerifiedCompilerConfig.v").read_text(
        encoding="utf-8"
    )
    for source, routes in (
        (
            driver_config,
            (
                "| VDefaultBand => BandCorrect.Opt_band loop",
                "| VSecondLevel => BandCorrect.Opt_band loop",
                "| VSecondLevelISS => BandCorrect.Opt_band_with_iss loop",
                "| VISS => BandCorrect.Opt_band_with_iss loop",
                "BandCorrect.Opt_identity_tiled_band loop",
                "BandCorrect.Opt_identity_tiled_band_with_iss loop",
                "| VPostTilingAffine => BandCorrect.Opt_post_tiling_affine_band loop",
                "| VPostTilingAffineISS => BandCorrect.Opt_post_tiling_affine_band_with_iss loop",
            ),
        ),
        (
            syntax_config,
            (
                "| VDefaultBand => SBandTilingOpt.opt loop",
                "| VSecondLevel => SBandTilingOpt.opt loop",
                "| VSecondLevelISS => SBandTilingOpt.opt_with_iss loop",
                "| VISS => SBandTilingOpt.opt_with_iss loop",
                "SBandTilingOpt.opt_identity_tiled loop",
                "SBandTilingOpt.opt_identity_tiled_with_iss loop",
                "| VPostTilingAffine => SBandTilingOpt.opt_post_tiling_affine loop",
                "| VPostTilingAffineISS => SBandTilingOpt.opt_post_tiling_affine_with_iss loop",
            ),
        ),
    ):
        for route in routes:
            require(source, route, "verified second-level config")

    unified_route = (
        "checked_tiling_schedule_sourceb_first_runtime_validate_route"
    )
    unified_correct = f"{unified_route}_correct"
    main_source = (ROOT / "syntax" / "SLoopMain.ml").read_text(encoding="utf-8")
    for forbidden in (
        "hinted_parallel_handlers",
        "current_parallel_handlers",
        "capture_silent_exception",
        "SLoopDispatch.run_selected_parallel_optimization",
        "SLoopDispatch.run_selected_parallel_current_optimization",
    ):
        if forbidden in main_source:
            raise AssertionError(
                f"product main retains a reconnectable legacy handler: {forbidden}"
            )
    band_source = (ROOT / "src" / "TilingBandScheduleValidator.v").read_text(
        encoding="utf-8"
    )
    runtime_source = (ROOT / "src" / "TilingBandDirectRuntime.v").read_text(
        encoding="utf-8"
    )
    route_constructors = coq_inductive_constructors(
        runtime_source,
        "tiling_band_validation_route",
    )
    if route_constructors != ["DirectBandAccepted", "GeneralScheduleAccepted", "Rejected"]:
        raise AssertionError(
            "tiling validation route must contain exactly "
            "DirectBandAccepted, GeneralScheduleAccepted, and Rejected, saw "
            f"{route_constructors}"
        )
    mixed_source = (
        ROOT / "src" / "TilingBandMixedSecondValidator.v"
    ).read_text(encoding="utf-8")
    phase_scalar_source = (
        ROOT / "src" / "TilingBandPhaseScalarValidator.v"
    ).read_text(encoding="utf-8")
    for path, source in (
        (ROOT / "src" / "TilingBandScheduleValidator.v", band_source),
        (ROOT / "src" / "TilingBandMixedSecondValidator.v", mixed_source),
        (ROOT / "src" / "TilingBandPhaseScalarValidator.v", phase_scalar_source),
        (ROOT / "src" / "TilingBandDirectRuntime.v", runtime_source),
    ):
        for forbidden in ("Admitted.", "Abort.", "Axiom "):
            if forbidden in source:
                raise AssertionError(
                    f"{path.relative_to(ROOT)} contains unfinished proof "
                    f"marker {forbidden!r}"
                )
    scalar_wrapper = coq_definition_body(
        band_source,
        "checked_tiling_sourceb_scalar_aware_direct",
    )
    for required in (
        "TilingCheck.check_pprog_tiling_sourceb",
        "infer_pprog_scalar_aware_common_shape",
        "check_pprog_scalar_aware_permutable_band_direct",
    ):
        require(
            scalar_wrapper,
            required,
            "safe scalar-aware source/shape/component gate",
        )
    complete_direct = coq_definition_body(
        runtime_source,
        "checked_tiling_sourceb_complete_direct_band_check",
    )
    require(
        complete_direct,
        "Legacy.checked_tiling_sourceb_scalar_aware_direct",
        "complete direct scalar-aware route",
    )
    require(
        complete_direct,
        "PhaseScalar.checked_tiling_sourceb_phase_scalar_extended_direct",
        "complete direct phase-class scalar-aware route",
    )
    for forbidden in (
        "Legacy.check_pprog_scalar_aware_permutable_band_direct",
        "Legacy.infer_pprog_scalar_aware_common_shape",
    ):
        if forbidden in complete_direct:
            raise AssertionError(
                "runtime bypasses the safe scalar-aware wrapper via "
                f"{forbidden}"
            )
    for path in (
        ROOT / "src" / "TilingBandScheduleValidator.v",
        ROOT / "src" / "TilingBandPhaseScalarValidator.v",
        ROOT / "src" / "TilingBandDirectRuntime.v",
        ROOT / "syntax" / "STilingBandSched.v",
        ROOT / "syntax" / "SBandTilingOpt.v",
        ROOT / "syntax" / "SParallelPolOpt.v",
        ROOT / "syntax" / "SLoopMain.ml",
        ROOT / "driver" / "Entry.ml",
    ):
        source = path.read_text(encoding="utf-8")
        for forbidden in (
            "TilingBandGeneralFallbackAccepted",
            "GeneralFallbackAccepted",
            '"general-fallback"',
        ):
            if forbidden in source:
                raise AssertionError(
                    f"tiling validation fallback remains in "
                    f"{path.relative_to(ROOT)}: {forbidden}"
                )
    midpoint_import_paths = (
        ROOT / "driver" / "PolOptBandTiling.v",
        ROOT / "driver" / "SBandTilingOptBridge.v",
        ROOT / "syntax" / "SBandTilingOpt.v",
        ROOT / "driver" / "ParallelPolOpt.v",
        ROOT / "driver" / "ParallelPolOptCorrect.v",
        ROOT / "driver" / "SParallelPolOptBridge.v",
        ROOT / "syntax" / "SParallelPolOpt.v",
    )
    identity_like_source_counts = {
        ROOT / "driver" / "PolOptBandTiling.v": 2,
        ROOT / "driver" / "SBandTilingOptBridge.v": 1,
        ROOT / "syntax" / "SBandTilingOpt.v": 1,
        ROOT / "driver" / "ParallelPolOpt.v": 1,
        ROOT / "driver" / "ParallelPolOptCorrect.v": 2,
        ROOT / "driver" / "SParallelPolOptBridge.v": 1,
        ROOT / "syntax" / "SParallelPolOpt.v": 1,
    }
    for path in midpoint_import_paths:
        source = path.read_text(encoding="utf-8")
        like_source_count = source.count(
            "from_openscop_like_source pol_source mid_scop"
        )
        expected_like_source_count = identity_like_source_counts.get(path, 0)
        if like_source_count != expected_like_source_count:
            raise AssertionError(
                "source-template midpoint import must be confined to "
                "identity-tiled helpers and their proofs/bridges: "
                f"{path.relative_to(ROOT)} has {like_source_count}, expected "
                f"{expected_like_source_count}"
            )
        require(
            source,
            "from_openscop_schedule_only pol_source mid_scop",
            f"globally aligned tiling midpoint import in {path.relative_to(ROOT)}",
        )
    for path in (
        ROOT / "driver" / "PolOptBandTiling.v",
        ROOT / "driver" / "SBandTilingOptBridge.v",
        ROOT / "syntax" / "SBandTilingOpt.v",
    ):
        source = path.read_text(encoding="utf-8")
        require(
            source,
            "try_identity_phase_pipeline_from_source_pol_band",
            f"dedicated identity-tiled midpoint import in {path.relative_to(ROOT)}",
        )
    identity_helper_specs = (
        (
            ROOT / "driver" / "PolOptBandTiling.v",
            "try_identity_phase_pipeline_from_source_pol_band",
        ),
        (
            ROOT / "syntax" / "SBandTilingOpt.v",
            "try_identity_phase_pipeline_from_source_pol_band",
        ),
        (
            ROOT / "driver" / "ParallelPolOpt.v",
            "try_identity_tiling_phase_pipeline_from_source_pol_poly",
        ),
        (
            ROOT / "syntax" / "SParallelPolOpt.v",
            "try_identity_tiling_phase_pipeline_from_source_pol_poly",
        ),
    )
    for path, helper in identity_helper_specs:
        body = coq_definition_body(path.read_text(encoding="utf-8"), helper)
        require(
            body,
            "from_openscop_like_source pol_source mid_scop",
            f"{path.relative_to(ROOT)} identity midpoint helper",
        )
        if "from_openscop_schedule_only" in body:
            raise AssertionError(
                f"{path.relative_to(ROOT)} identity midpoint helper mixes "
                "source-template and schedule-only importers"
            )
    ordinary_helper_specs = (
        (
            ROOT / "driver" / "PolOptBandTiling.v",
            "try_phase_pipeline_from_source_pol_band",
        ),
        (
            ROOT / "syntax" / "SBandTilingOpt.v",
            "try_phase_pipeline_from_source_pol_band",
        ),
        (
            ROOT / "driver" / "ParallelPolOpt.v",
            "try_phase_pipeline_from_source_pol_poly",
        ),
        (
            ROOT / "syntax" / "SParallelPolOpt.v",
            "try_phase_pipeline_from_source_pol_poly",
        ),
    )
    for path, helper in ordinary_helper_specs:
        body = coq_definition_body(path.read_text(encoding="utf-8"), helper)
        require(
            body,
            "from_openscop_schedule_only pol_source mid_scop",
            f"{path.relative_to(ROOT)} ordinary midpoint helper",
        )
        if "from_openscop_like_source" in body:
            raise AssertionError(
                f"{path.relative_to(ROOT)} ordinary midpoint helper uses "
                "the identity-only source-template importer"
            )
    sloop_main = (ROOT / "syntax" / "SLoopMain.ml").read_text(encoding="utf-8")
    debug_tiling = definition_body(sloop_main, "debug_band_tiling_runtime")
    for required in (
        "if identity_tiled then",
        "PolyLang.from_openscop_like_source",
        "PolyLang.from_openscop_schedule_only",
        'if identity_tiled then "source-like" else "schedule-only"',
    ):
        require(
            debug_tiling,
            required,
            "identity-aware band-tiling debug importer",
        )
    for path in (
        ROOT / "syntax" / "STilingBandSched.v",
        ROOT / "syntax" / "SLoopMain.ml",
        ROOT / "driver" / "Entry.ml",
    ):
        source = path.read_text(encoding="utf-8")
        for forbidden in (
            "via_validate_tiling",
            "checked_tiling_schedule_canonical_validate",
            "checked_tiling_validate_general_fallback",
        ):
            if forbidden in source:
                raise AssertionError(
                    f"hidden legacy tiling validator remains in "
                    f"{path.relative_to(ROOT)}: {forbidden}"
                )
    common_direct_check = coq_definition_body(
        runtime_source,
        "checked_tiling_sourceb_first_direct_band_check",
    )
    for needle in (
        "check_pprog_pluto_permutable_tiling_bands_direct",
        "check_pprog_second_level_schedule_directb",
        "check_pinstr_list_pluto_componentwise_permutable_bands_direct",
    ):
        require(
            common_direct_check,
            needle,
            "direct ordinary and second-level dispatch",
        )
    direct_shape = coq_definition_body(
        band_source,
        "check_pprog_second_level_schedule_directb",
    )
    for needle in (
        "check_common_second_level_recipe_sizesb",
        "check_common_band_startb",
        "SecondLevelGrouped",
        "SecondLevelInterleaved",
        "check_pinstr_list_second_level_schedule_directb",
    ):
        require(
            direct_shape,
            needle,
            "uniform-layout direct second-level classifier",
        )
    zero_erasure = coq_definition_body(
        band_source,
        "check_pinstr_list_second_level_schedule_zero_erasureb",
    )
    for needle in (
        "second_level_expected_schedules",
        "check_schedule_masks_eqb",
        "check_schedule_lists_after_zero_erasureb",
    ):
        require(
            zero_erasure,
            needle,
            "program-wide strict-zero schedule normalization",
        )
    for forbidden in (
        "check_pprog_permutable_tiling_bands_via_validate_tiling",
        "checked_tiling_sourceb_first_band_check",
    ):
        if forbidden in common_direct_check:
            raise AssertionError(
                f"DirectBandAccepted path contains affine fallback {forbidden}"
            )

    semantic_direct_check = coq_definition_body(
        band_source,
        "checked_tiling_sourceb_semantic_band_direct",
    )
    for needle in (
        "check_pprog_tiling_sourceb",
        "infer_pprog_ordinary_semantic_band_shape",
        "infer_pprog_second_level_semantic_band_shape",
        "check_semantic_band_components_direct",
    ):
        require(
            semantic_direct_check,
            needle,
            "semantic-band direct dispatch",
        )

    semantic_component_check = coq_definition_body(
        band_source,
        "check_semantic_band_components_direct_aligned",
    )
    for needle in (
        "validate_semantic_band_entry_list_components_direct_from",
        "BandAffine.check_valid_access",
    ):
        require(
            semantic_component_check,
            needle,
            "semantic-band component checker",
        )

    componentwise_direct_check = coq_definition_body(
        band_source,
        "check_pinstr_list_pluto_componentwise_permutable_bands_direct",
    )
    for needle in (
        "validate_instr_band_entry_list_components_direct_from",
        "BandAffine.check_valid_access",
    ):
        require(
            componentwise_direct_check,
            needle,
            "componentwise permutable-band checker",
        )

    mixed_direct_check = coq_definition_body(
        mixed_source,
        "check_pprog_mixed_second_level_direct",
    )
    phase_ordinary_direct_check = coq_definition_body(
        mixed_source,
        "check_pprog_phase_separated_ordinary_direct",
    )
    for needle in (
        "Core.TilingCheck.check_pprog_tiling_sourceb",
        "Core.check_pprog_tiling_schedule_stripminedb",
        "Core.infer_pinstr_list_tiling_bands",
        "Core.check_uniform_schedule_arityb",
        "check_phase_class_consistencyb",
        "Core.check_pinstr_list_pluto_componentwise_permutable_bands_direct",
    ):
        require(
            phase_ordinary_direct_check,
            needle,
            "phase-separated ordinary direct checker",
        )
    for needle in (
        "Core.TilingCheck.check_pprog_tiling_sourceb",
        "infer_pprog_mixed_second_level_shape",
        "Core.check_pinstr_list_pluto_componentwise_permutable_bands_direct",
    ):
        require(
            mixed_direct_check,
            needle,
            "mixed second-level direct checker",
        )

    for name, body in (
        ("common direct checker", common_direct_check),
        ("semantic direct checker", semantic_direct_check),
        ("semantic component checker", semantic_component_check),
        ("componentwise direct checker", componentwise_direct_check),
        ("phase-separated ordinary direct checker", phase_ordinary_direct_check),
        ("mixed second-level direct checker", mixed_direct_check),
    ):
        for forbidden in (
            "checked_tiling_validate",
            "validate_general",
            "via_validate_tiling",
            "Canonical",
            "general_fallback",
            "FallbackAccepted",
        ):
            if forbidden in body:
                raise AssertionError(
                    f"{name} transitively exposes forbidden alternate "
                    f"tiling validation call {forbidden}"
                )

    complete_direct_check = coq_definition_body(
        runtime_source,
        "checked_tiling_sourceb_complete_direct_band_check",
    )
    for needle in (
        "checked_tiling_sourceb_first_direct_band_check",
        "check_pprog_phase_separated_ordinary_direct",
        "checked_tiling_sourceb_semantic_band_direct",
        "check_pprog_mixed_second_level_direct",
    ):
        require(
            complete_direct_check,
            needle,
            "complete direct-only tiling dispatcher",
        )
    for forbidden in (
        "checked_tiling_sourceb_first_band_check",
        "checked_tiling_schedule_canonical_validate",
        "checked_tiling_validate",
        "FallbackAccepted",
    ):
        if forbidden in complete_direct_check:
            raise AssertionError(
                "complete direct-only tiling dispatcher contains forbidden "
                f"fallback {forbidden}"
            )

    direct_route = "checked_tiling_schedule_sourceb_first_direct_runtime_validate_route"
    general_dispatcher = coq_definition_body(runtime_source, unified_route)
    for needle in (
        "checked_tiling_sourceb_complete_direct_band_check",
        "if direct_ok then pure DirectBandAccepted",
        "if has_tiling_coordinatesb ws then",
        "BIND schedule_ok <- Legacy.Base.checked_tiling_validate_outer before after ws",
        "if schedule_ok then GeneralScheduleAccepted else Rejected",
    ):
        require(general_dispatcher, needle, "proved actual-schedule fallback")
    require(runtime_source, "Legacy.Base.checked_tiling_validate_outer_correct",
            "actual-schedule fallback refinement proof")
    direct_dispatcher = coq_definition_body(runtime_source, direct_route)
    require(
        direct_dispatcher,
        "checked_tiling_sourceb_complete_direct_band_check",
        "direct band-only runtime dispatcher",
    )
    for forbidden in (
        "Legacy.checked_tiling_sourceb_first_band_check",
        "Legacy.Canonical.checked_tiling_schedule_canonical_validate",
        "Legacy.Base.checked_tiling_validate",
        "GeneralFallbackAccepted",
        '"general-fallback"',
    ):
        if forbidden in direct_dispatcher:
            raise AssertionError(
                f"runtime tiling dispatcher retains forbidden fallback {forbidden}"
            )

    for path in (
        ROOT / "syntax" / "STilingBandSched.v",
        ROOT / "syntax" / "SBandTilingOpt.v",
        ROOT / "syntax" / "SParallelPolOpt.v",
    ):
        labeler = coq_definition_body(
            path.read_text(encoding="utf-8"),
            "tiling_validation_route_label",
        )
        for needle in ("GeneralFallbackAccepted", '"general-fallback"'):
            if needle in labeler:
                raise AssertionError(
                    f"fallback Coq label mapping remains in {path.name}: {needle}"
                )

    for path in (ROOT / "syntax" / "SLoopMain.ml", ROOT / "driver" / "Entry.ml"):
        classifier = definition_body(
            path.read_text(encoding="utf-8"),
            "classify_tiling_band_route",
        )
        for needle in (
            "GeneralFallbackAccepted",
            'accept_if_wf "general-fallback"',
        ):
            if needle in classifier:
                raise AssertionError(
                    f"fallback route mapping remains in {path.name}: {needle}"
                )

    require(
        (ROOT / "extraction" / "extraction.v").read_text(encoding="utf-8"),
        '"TilingValidationRoute.record_coq_label"',
        "extracted tiling route recorder hook",
    )
    require(
        (ROOT / "syntax" / "TilingValidationRoute.ml").read_text(encoding="utf-8"),
        '"[tiling-validation] route=%s\\n"',
        "tiling route stderr format",
    )

    for path, prefix in (
        (ROOT / "driver" / "VerifiedParallelCompilerConfig.v", "ParallelCore.Opt_"),
        (ROOT / "syntax" / "SVerifiedParallelCompilerConfig.v", "SParallelPolOpt.opt_"),
    ):
        source = path.read_text(encoding="utf-8")
        for suffix in (
            "parallel_current_identity_tiled loop d",
            "parallel_current_identity_tiled_with_iss loop d",
            "parallel_current loop d",
            "parallel_current_with_iss loop d",
            "parallel_current_post_tiling_affine loop d",
            "parallel_current_post_tiling_affine_with_iss loop d",
            "parallel_current_many_identity_tiled loop dims",
            "parallel_current_many_identity_tiled_with_iss loop dims",
            "parallel_current_many loop dims",
            "parallel_current_many_with_iss loop dims",
            "parallel_current_many_post_tiling_affine loop dims",
            "parallel_current_many_post_tiling_affine_with_iss loop dims",
            "vector_current_identity loop d",
            "vector_current_identity_tiled loop d",
            "vector_current_identity_tiled_with_iss loop d",
            "vector_current_affine loop d",
            "vector_current loop d",
            "vector_current_post_tiling_affine loop d",
            "vector_current_post_tiling_affine_with_iss loop d",
            "vector_current_identity_with_iss loop d",
            "vector_current_affine_with_iss loop d",
            "vector_current_with_iss loop d",
        ):
            require(
                source,
                prefix + suffix,
                f"tiling-bearing parallel config in {path.relative_to(ROOT)}",
            )

    sequential_config_body = definition_body(
        main_source, "verified_sequential_config_of_route"
    )
    if "force_legacy_generic_tiling" in sequential_config_body:
        raise AssertionError("legacy compatibility flag must not bypass band-first dispatch")
    if re.search(r"\bRawDefault\b", sequential_config_body):
        raise AssertionError("the generic-primary RawDefault route must not be CLI-selectable")
    require(sequential_config_body, "RawDefaultBand", "normal default band route")
    syntax_compile_body = coq_definition_body(
        (ROOT / "syntax" / "SVerifiedCompilerConfig.v").read_text(
            encoding="utf-8"
        ),
        "compile_verified",
    )
    affine_iss_route = "VAffineISS => SPolOpt.opt_with_iss loop"
    require(
        syntax_compile_body,
        affine_iss_route,
        "affine-with-ISS route in syntax verified compiler",
    )
    if syntax_compile_body.count("SPolOpt.opt_with_iss") != 1:
        raise AssertionError(
            "SPolOpt.opt_with_iss must be used only by the no-tiling VAffineISS route"
        )
    proof_compile_body = coq_definition_body(
        (ROOT / "driver" / "VerifiedCompilerConfig.v").read_text(
            encoding="utf-8"
        ),
        "compile_verified",
    )
    proof_affine_iss_route = (
        "VAffineISS => CoreCorrect.Core.Opt_with_iss loop"
    )
    require(
        proof_compile_body,
        proof_affine_iss_route,
        "affine-with-ISS route in proved verified compiler",
    )
    if proof_compile_body.count("CoreCorrect.Core.Opt_with_iss") != 1:
        raise AssertionError(
            "CoreCorrect.Core.Opt_with_iss must be used only by the "
            "no-tiling VAffineISS route"
        )
    for path, old_route, band_route in (
        (
            ROOT / "driver" / "VerifiedCompilerConfig.v",
            "VDefault => CoreCorrect.Core.Opt loop",
            "VDefault => BandCorrect.Opt_band loop",
        ),
        (
            ROOT / "syntax" / "SVerifiedCompilerConfig.v",
            "VDefault => SPolOpt.opt loop",
            "VDefault => SBandTilingOpt.opt loop",
        ),
    ):
        source = path.read_text(encoding="utf-8")
        if old_route in source:
            raise AssertionError(
                f"RawDefault in {path.relative_to(ROOT)} bypasses band-first dispatch"
            )
        require(
            source,
            band_route,
            f"RawDefault band-first dispatch in {path.relative_to(ROOT)}",
        )
    for path in (
        ROOT / "syntax" / "SLoopMain.ml",
        ROOT / "driver" / "Entry.ml",
        ROOT / "syntax" / "SVerifiedCompilerConfig.v",
        ROOT / "syntax" / "SVerifiedParallelCompilerConfig.v",
        ROOT / "driver" / "VerifiedCompilerConfig.v",
        ROOT / "driver" / "VerifiedParallelCompilerConfig.v",
    ):
        source = path.read_text(encoding="utf-8")
        for pattern, label in (
            (r"\bSPolOpt\.opt\b", "legacy syntax tiling optimizer"),
            (r"\bSPolOpt\.opt_poly\b", "legacy syntax PolyLang tiling optimizer"),
            (r"\bSPolOpt\.opt_scop\b", "legacy syntax OpenScop tiling optimizer"),
            (r"\bPolOpt\.Opt\b", "legacy generic tiling optimizer"),
            (r"\bCPolOpt\.opt\b", "legacy C tiling optimizer"),
            (r"\bPolOptCanonicalTiling\b", "legacy canonical tiling optimizer"),
        ):
            if re.search(pattern, source):
                raise AssertionError(
                    f"product entrypoint {path.relative_to(ROOT)} reaches {label}"
                )
        if path != ROOT / "syntax" / "SVerifiedCompilerConfig.v" and re.search(
            r"\bSPolOpt\.opt_with_iss\b", source
        ):
            raise AssertionError(
                f"product entrypoint {path.relative_to(ROOT)} reaches "
                "legacy syntax ISS tiling optimizer"
            )
    for path in (
        ROOT / "src" / "TilingBandDirectRuntime.v",
        ROOT / "driver" / "PolOptBandTiling.v",
        ROOT / "driver" / "ParallelPolOpt.v",
        ROOT / "syntax" / "STilingBandSched.v",
        ROOT / "syntax" / "SBandTilingOpt.v",
        ROOT / "syntax" / "SParallelPolOpt.v",
        ROOT / "driver" / "Entry.ml",
        ROOT / "syntax" / "SLoopMain.ml",
    ):
        require(
            path.read_text(encoding="utf-8"),
            unified_route,
            f"unified sourceb-first route in {path.relative_to(ROOT)}",
        )

    for path, dummy, selector, requires_observation in (
        (
            ROOT / "syntax" / "SBandTilingOpt.v",
            "SPolIRs.Loop.dummy",
            "prepared_codegen_after_tiling_route",
            True,
        ),
        (
            ROOT / "syntax" / "SParallelPolOpt.v",
            "PolyLang.dummy",
            "select_after_tiling_route",
            True,
        ),
        (
            ROOT / "driver" / "PolOptBandTiling.v",
            "LoopIR.dummy",
            "prepared_codegen_after_tiling_route",
            False,
        ),
        (
            ROOT / "driver" / "ParallelPolOpt.v",
            "PolyLang.dummy",
            "select_after_tiling_route",
            True,
        ),
    ):
        source = path.read_text(encoding="utf-8")
        if "reject_tiling_then" in source:
            raise AssertionError(
                f"{path.name} retains the old rejection continuation"
            )
        if "affine_only_opt_prepared_from_poly" in source:
            raise AssertionError(
                f"{path.name} can still return an affine-only result after "
                "a tiling failure"
            )
        for pattern, label in (
            (r"\bpure\s+pol_(?:mid|source)\b", "source or midpoint result"),
            (
                r"prepared_codegen\s*"
                r"\(\s*PolyLang\.current_view_pprog\s+pol_(?:mid|source)\s*\)",
                "prepared source or midpoint result",
            ),
        ):
            if re.search(pattern, source, re.MULTILINE):
                raise AssertionError(
                    f"{path.name} retains a tiling rejection path returning {label}"
                )
        rejected = coq_definition_body(source, "reject_tiling")
        if requires_observation:
            require(
                rejected,
                "observe_tiling_validation_route TilingSched.Rejected",
                "rejected tiling telemetry",
            )
        require(rejected, "res_to_alarm", "fail-closed tiling rejection")
        require(rejected, dummy, "fixed tiling rejection dummy")
        for forbidden in ("pol_mid", "pol_source", "fallback"):
            if forbidden in rejected:
                raise AssertionError(
                    f"{path.name} rejection still carries {forbidden}"
                )

        selected = coq_definition_body(source, selector)
        require(selected, "TilingSched.Rejected", f"{selector} rejected branch")
        require(selected, "res_to_alarm", f"{selector} fail-closed branch")
        require(selected, dummy, f"{selector} fixed rejection dummy")
        for forbidden in ("pol_mid", "pol_source", "fallback"):
            if forbidden in selected:
                raise AssertionError(
                    f"{path.name} {selector} still carries {forbidden}"
                )

        post_affine = coq_definition_body(source, "reject_post_tiling_affine")
        require(post_affine, "res_to_alarm", "post-tiling affine rejection")
        require(post_affine, dummy, "post-tiling affine fixed dummy")
        for forbidden in (
            "pol_mid",
            "pol_source",
            "fallback",
            "observe_tiling_validation_route",
        ):
            if forbidden in post_affine:
                raise AssertionError(
                    f"{path.name} post-tiling affine rejection still carries "
                    f"{forbidden}"
                )

    for path, dummy, selector, requires_observation in (
        (
            ROOT / "extraction" / "SBandTilingOpt.ml",
            "SPolIRs.SPolIRs.Loop.dummy",
            "prepared_codegen_after_tiling_route",
            True,
        ),
        (
            ROOT / "extraction" / "SParallelPolOpt.ml",
            "PolyLang.dummy",
            "select_after_tiling_route",
            True,
        ),
        (
            ROOT / "extraction" / "PolOptBandTiling.ml",
            "LoopIR.dummy",
            "prepared_codegen_after_tiling_route",
            False,
        ),
        (
            ROOT / "extraction" / "ParallelPolOpt.ml",
            "PolyLang.dummy",
            "select_after_tiling_route",
            False,
        ),
    ):
        source = path.read_text(encoding="utf-8")
        for forbidden in (
            "reject_tiling_then",
            "affine_only_opt_prepared_from_poly",
            "CoreAlarmed.Base.pure pol_mid",
            "CoreAlarmed.Base.pure pol_source",
            "PrepareCore.prepared_codegen pol_mid",
            "PrepareCore.prepared_codegen pol_source",
            "checked_affine_schedule pol_source",
            "res_to_alarm pol_mid",
            "res_to_alarm pol_source",
            "tiling_band_validation_route_acceptsb",
        ):
            if forbidden in source:
                raise AssertionError(
                    f"stale extracted tiling fallback remains in "
                    f"{path.relative_to(ROOT)}: {forbidden}"
                )
        rejected = extracted_definition_body(source, "reject_tiling")
        require(rejected, "res_to_alarm", f"{path.name} extracted rejection alarm")
        require(rejected, dummy, f"{path.name} extracted rejection dummy")
        if requires_observation:
            require(
                rejected,
                "observe_tiling_validation_route TilingSched.Rejected",
                f"{path.name} extracted rejected-route observation",
            )
        selected = extracted_definition_body(source, selector)
        require(
            selected,
            "TilingSched.Rejected",
            f"{path.name} extracted selector rejection",
        )
        require(selected, "res_to_alarm", f"{path.name} extracted selector alarm")
        require(selected, dummy, f"{path.name} extracted selector dummy")
        post_affine = extracted_definition_body(
            source,
            "reject_post_tiling_affine",
        )
        require(
            post_affine,
            "res_to_alarm",
            f"{path.name} extracted post-affine rejection",
        )
        require(
            post_affine,
            dummy,
            f"{path.name} extracted post-affine dummy",
        )
        if "observe_tiling_validation_route" in post_affine:
            raise AssertionError(
                f"{path.name} extracted post-affine rejection reports the "
                "already-recorded tiling route twice"
            )

    for path in (
        ROOT / "src" / "TilingBandDirectRuntime.v",
        ROOT / "driver" / "PolOptBandTiling.v",
        ROOT / "driver" / "ParallelPolOptCorrect.v",
    ):
        require(
            path.read_text(encoding="utf-8"),
            unified_correct,
            f"unified sourceb-first proof in {path.relative_to(ROOT)}",
        )

    for path in (
        ROOT / "syntax" / "SBandTilingOpt.v",
        ROOT / "syntax" / "SParallelPolOpt.v",
    ):
        require(
            path.read_text(encoding="utf-8"),
            "observe_tiling_validation_route",
            f"exact runtime route observation in {path.relative_to(ROOT)}",
        )

    require(
        (ROOT / "extraction" / "extraction.v").read_text(encoding="utf-8"),
        "TilingValidationRoute.record_coq_label",
        "extracted route recorder",
    )
    require(
        main_source,
        "TilingValidationRoute.capture",
        "final-candidate route reporting",
    )

    for route in (
        "try_verified_parallel_current_compile",
        "try_verified_parallel_current_many_compile",
        "try_verified_vector_current_compile",
    ):
        route_body = definition_body(main_source, route)
        require_count(
            route_body,
            "TilingValidationRoute.report",
            0,
            f"unreported candidate probe {route}",
        )
        for needle in (
            "TilingValidationRoute.capture_result",
            "verified_candidate_or_raise",
        ):
            require(
                route_body,
                needle,
                f"fail-closed producer handling in candidate probe {route}",
            )
    require_count(
        definition_body(main_source, "run_selected_sequential_loop_compiler"),
        "TilingValidationRoute.report",
        1,
        "single report in the shared sequential compiler dispatcher",
    )
    for route in (
        "run_verified_hinted_parallel_optimization_with",
        "run_verified_hinted_multipar_parallel_optimization_with",
        "run_selected_vector_optimization",
        "run_selected_parallel_current_optimization",
        "run_selected_vector_current_optimization",
    ):
        require_count(
            definition_body(main_source, route),
            "TilingValidationRoute.report",
            1,
            f"single final-candidate report {route}",
        )
    for wrapper, implementation in (
        (
            "run_verified_hinted_parallel_optimization",
            "run_verified_hinted_parallel_optimization_with",
        ),
        (
            "run_verified_hinted_multipar_parallel_optimization",
            "run_verified_hinted_multipar_parallel_optimization_with",
        ),
    ):
        wrapper_body = definition_body(main_source, wrapper)
        require_count(
            wrapper_body,
            "TilingValidationRoute.report",
            0,
            f"no duplicate final-candidate report in wrapper {wrapper}",
        )
        require(
            wrapper_body,
            implementation,
            f"thin wrapper {wrapper} reaches reporting implementation",
        )
    for route in (
        "run_selected_sequential_loop_optimization",
        "run_requested_sequential_loop_optimization",
    ):
        route_body = definition_body(main_source, route)
        require_count(
            route_body,
            "TilingValidationRoute.report",
            0,
            f"no duplicate report in sequential wrapper {route}",
        )
    require(
        definition_body(main_source, "run_selected_sequential_loop_optimization"),
        "run_selected_sequential_loop_compiler",
        "ordinary postpass uses the shared sequential compiler dispatcher",
    )
    requested_sequential = definition_body(
        main_source, "run_requested_sequential_loop_optimization"
    )
    for needle in (
        "run_selected_sequential_loop_compiler",
        "run_selected_sequential_loop_optimization",
    ):
        require(
            requested_sequential,
            needle,
            "checked unroll-jam and ordinary postpasses share final reporting",
        )

    consumer_failure_classifier = definition_body(
        main_source, "is_consumer_candidate_failure"
    )
    for needle in (
        "CertcheckerConfig.CertCheckerFailure",
        '"Parallel validation failed"',
        '"Annotated parallel codegen produced non-affine instruction trace loop"',
        '"Annotated vector codegen produced a non-affine trace, a non-innermost vector loop, or no vector loop"',
    ):
        require(
            consumer_failure_classifier,
            needle,
            "explicit allowlist for consumer candidate failures",
        )

    candidate_result_handler = definition_body(
        main_source, "verified_candidate_or_raise"
    )
    for needle in (
        "is_consumer_candidate_failure exn",
        "TilingValidationRoute.report routes",
        "raise exn",
        "None",
    ):
        require(
            candidate_result_handler,
            needle,
            "candidate probes preserve producer failures",
        )

    explicit_failure_reporter = definition_body(
        main_source, "report_explicit_current_failure"
    )
    for needle in (
        "is_consumer_candidate_failure exn",
        "TilingValidationRoute.report routes",
        "report_consumer ()",
    ):
        require(
            explicit_failure_reporter,
            needle,
            "producer rejection takes precedence over explicit consumer rejection",
        )
    for route in (
        "run_selected_parallel_current_optimization",
        "run_selected_vector_current_optimization",
    ):
        require(
            definition_body(main_source, route),
            "report_explicit_current_failure exn routes",
            f"producer rejection attribution in {route}",
        )

    hinted_multipar_body = definition_body(
        main_source, "run_verified_hinted_multipar_parallel_optimization_with"
    )
    for needle in (
        "| Some (pl, routes, _accepted_hint) ->",
        "(pl, true)",
        "sequential_fallback route loop",
    ):
        require(
            hinted_multipar_body,
            needle,
            "non-strict hinted multipar accepts a certified searched dimension "
            "or skips to the verified sequential route",
        )

    standalone_body = definition_body(main_source, "run_tiling_validator")
    for needle in (
        "TilingValidationRoute.capture",
        "tiling_forward_scops",
        "TilingValidationRoute.report",
    ):
        require(standalone_body, needle, "standalone OpenScop tiling validator")

    suite_runner = (
        ROOT / "tools" / "second_level_tiling" / "run_second_level_tile_suite.py"
    ).read_text(encoding="utf-8")
    require(
        suite_runner,
        "check_standalone_formal_route(",
        "standalone formal-route dynamic regression",
    )
    require(
        suite_runner,
        "check_second_level_diamond_route_matrix(",
        "second-level diamond current/strict route matrix",
    )
    standalone_regression = (
        ROOT
        / "tools"
        / "second_level_tiling"
        / "check_standalone_formal_route.py"
    ).read_text(encoding="utf-8")
    for needle in (
        '"formal: PASS"',
        "AFFINE_PLUTO_FLAGS",
        "TILING_PLUTO_FLAGS",
        "expected_route=BAND_ROUTE",
        "if route_lines != [expected_route]",
        '"--validate-tiling-openscop"',
    ):
        require(
            standalone_regression,
            needle,
            "standalone formal-route dynamic regression",
        )

    for route in (
        "RawParallelCurrentIdentityTiledISS",
        "RawParallelCurrentManyIdentityTiledISS",
        "RawVectorCurrentIdentityTiledISS",
    ):
        require(main_source, route, "identity-tiled ISS parallel/vector dispatch")

    hinted_producer = definition_body(
        main_source, "scheduled_scop_and_hints_of_route"
    )
    for needle in (
        "route_uses_post_tiling_affine route",
        "route_has_iss route",
        "identity_schedule_input_scop route",
        "post_tiling_affine_scop_scheduler_with_parallel_hint",
        "post_tiling_affine_scop_scheduler_with_vector_hint",
        "run_pluto_phase_pipeline_with_parallel_hint",
        "run_pluto_phase_pipeline_with_vector_hint",
    ):
        require(
            hinted_producer,
            needle,
            "normalized scheduled-OpenScop and hint producer",
        )
    for route in (
        "parallel_scop_and_hint_dims_of_route",
        "vector_hint_dims_of_route",
        "dump_scheduled_openscop_with_parallel",
        "dump_scheduled_openscop_with_vector",
    ):
        require(
            definition_body(main_source, route),
            "scheduled_scop_and_hints_of_route",
            route,
        )

    vector_config = definition_body(
        main_source, "verified_vector_current_config_of_route"
    )
    for constructor in (
        "RawVectorCurrentIdentityTiledISS",
        "RawVectorCurrentPostTilingAffineISS",
        "RawVectorCurrentDefaultISS",
    ):
        require(vector_config, constructor, "proved vector config dispatch")
    for route in (
        "try_verified_vector_current_compile",
        "run_selected_vector_optimization",
    ):
        require(
            definition_body(main_source, route),
            "VerifiedParallelCompiler.compile" if route == "try_verified_vector_current_compile" else "try_verified_vector_current_compile",
            "proved vector config execution",
        )
    automatic_vector = definition_body(main_source, "run_selected_vector_optimization")
    require(automatic_vector, "let candidates = hinted_dims", "hint-only automatic vector execution")
    if "int_range" in automatic_vector:
        raise AssertionError("automatic vector execution must not scan unhinted dimensions")
    require(
        definition_body(main_source, "run_selected_vector_current_optimization"),
        "VerifiedParallelCompiler.compile",
        "fail-closed explicit vector-current execution",
    )

    print(
        "[second-level-route-static] PASS "
        "expected=flags-forwarded,band-first-dispatch,unique-final-report,"
        "affine-ISS-no-tiling-route,pluto-default-no-rar "
        "actual=all-static-route-contracts-matched coverage=static-route-contract "
        "interpretation=source-and-extracted-entrypoints-follow-the-declared-routes"
    )


if __name__ == "__main__":
    main()
