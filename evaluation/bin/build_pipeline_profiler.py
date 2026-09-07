#!/usr/bin/env python3
"""Instrument actual compiler stages, including parallel validation, in isolation.

The native overlay wraps extracted entry points without editing their bodies.
It runs the normal driver once, not --profile-stages' diagnostic re-execution.
"""

import re
import sys


def label_affine_calls(source):
    """Label audited phase call sites, never infer phases from call order.

    The low-level affine wrapper remains a catch-all. An unlabelled standalone
    affine invocation therefore remains visible and blocks the final dataset.
    """
    for name, first, second, stage in [
            ("validate", "pol_source", "pol_mid", "affine_pre_validation"),
            ("validate", "pol", "pol'", "affine_pre_validation"),
            ("validate_general", "pol_posttile", "pol_after", "affine_post_validation")]:
        pattern = (r"(?P<call>(?:\b[A-Z]\w*\.)*ValidatorCore\." + name +
                   r"\s+" + re.escape(first) + r"\s+" + re.escape(second) + r"(?![\w']))")
        source = re.sub(pattern, lambda m: 'PipelineMeasure.region "' + stage +
                        '" (fun () -> ' + m.group("call") + ')', source)
    return source


def wrap_all(source, name, arity, label, measurement_module="PipelineMeasure"):
    """Wrap all module-level copies of a named extracted definition.

    Extraction sometimes expands a functor into a nested module. Find its next
    declaration or enclosing end at the same or lower indentation, not an inner
    expression-level let. Insert backwards to preserve the original offsets.
    """
    pattern = re.compile(r"(?m)^( *)let (?:rec )?" + re.escape(name) + r"(?=[\s:=(])")
    matches = list(pattern.finditer(source))
    for match in reversed(matches):
        indent = match.group(1)
        tail = source[match.end():]
        boundaries = re.finditer(r"(?m)^( *)(?:\(\*\* val |end\b|let |type |module |open )", tail)
        end = next((boundary for boundary in boundaries
                    if len(boundary.group(1)) <= len(indent)), None)
        position = match.end() + end.start() if end else len(source)
        args = ["measure_arg_" + str(i) for i in range(arity)]
        wrapper = ("\n" + indent + "let " + name + " " + " ".join(args) + " =\n" + indent +
                   '  ' + measurement_module + '.region "' + label + '" (fun () ->\n' + indent +
                   "    " + name + " " + " ".join(args) + ")\n\n")
        source = source[:position] + wrapper + source[position:]
    return source


def instrument(relative, source):
    if relative == "syntax/SLoopMain.ml":
        anchor = "let () =\n  try\n"
        if source.count(anchor) != 1:
            raise ValueError("Driver initialization changed; review instrumentation.")
        source = source.replace(anchor, "let () =\n  PipelineMeasure.start ();\n  try\n", 1)
        # The scoped adapter separately checks the original producer schedule.
        # The lexical route explicitly tells us whether this is pre/post tiling.
        call = "V.validate_general old_pol proposed_pol"
        if source.count(call) != 1:
            raise ValueError("Scoped original-proposal validation call site changed.")
        return source.replace(call,
            'PipelineMeasure.region (if route_has_tiling route then "affine_post_validation" '
            'else "affine_pre_validation") (fun () -> ' + call + ')', 1)
    if relative == "driver/Scheduler.ml":
        for name, arity, payload in [
                ("run_pluto_scop", 2, 'Okk scop -> save "after" scop'),
                ("run_pluto_scop_with_phase_dumps", 2,
                 'Okk (mid, tiled, after) -> save "mid" mid; save "tiled" tiled; save "after" after'),
                ("run_pluto_scop_with_loop_hint", 4,
                 'Okk (scop, _) -> save "after" scop')]:
            if not re.search(r"(?m)^let " + name + r" ", source):
                raise ValueError("Scheduler boundary missing: " + name)
            source = wrap_all(source, name, arity, "pluto")
            args = ["measure_arg_" + str(i) for i in range(arity)]
            anchor = 'let ' + name + ' ' + ' '.join(args) + ' =\n  PipelineMeasure.region "pluto" (fun () ->\n    ' + name + ' ' + ' '.join(args) + ')'
            flags, inscop = args[-2:]
            replacement = ('let ' + name + ' ' + ' '.join(args) + ' =\n'
                '  let capture = PipelineMeasure.capture_begin "' + name + '" ' + flags + '\n'
                '    (fun path -> OpenScopPrinter.openscop_printer path ' + inscop + ') in\n'
                '  let result = PipelineMeasure.region "pluto" (fun () ->\n'
                '    ' + name + ' ' + ' '.join(args) + ') in\n'
                '  PipelineMeasure.capture_result capture (fun base ->\n'
                '    let save tag scop = OpenScopPrinter.openscop_printer (base ^ "." ^ tag ^ ".scop") scop in\n'
                '    match result with ' + payload + ' | Err _ -> ());\n'
                '  result')
            if source.count(anchor) != 1:
                raise ValueError("Capture wrapper anchor differs: " + name)
            source = source.replace(anchor, replacement, 1)
        source = wrap_all(source, "run_pluto_bridge", 2, "pluto")
    elif relative.startswith("extraction/"):
        source = label_affine_calls(source)
        # These names are checked against both ordinary and expanded modules.
        specs = [("extractor", 1, "extraction"),
                 ("check_pprog_parallel_currentb", 2, "parallel_validation"),
                 ("checked_tiling_schedule_sourceb_first_direct_runtime_validate_route", 3, "tiling_validation"),
                 ("checked_tiling_schedule_sourceb_first_runtime_validate_route", 3, "tiling_validation")]
        if relative in ("extraction/AffineValidator.ml", "extraction/ParallelCodegen.ml"):
            specs += [("validate", 2, "affine_validation"),
                      ("validate_tiling", 2, "affine_validation")]
        if relative in ("extraction/CodeGen.ml", "extraction/ParallelCodegen.ml"):
            specs += [("codegen", 1, "codegen")]
        for name, arity, label in specs:
            source = wrap_all(source, name, arity, label)
    return source


if __name__ == "__main__":
    import build_vpl_profiler
    sys.argv.extend(["--flavor", "pipeline"])
    build_vpl_profiler.main()
