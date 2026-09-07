#!/usr/bin/env python3
"""Build an isolated native overlay with nested monotonic VPL instrumentation."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shlex
import shutil
import subprocess


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def wrap(source, name, arity, label, *, indent="", occurrence=0, metrics=None):
    """Eta-expand a shadowing wrapper after a complete module-level definition.

    The original definition and recursive body remain byte-for-byte unchanged.
    Later uses resolve to the wrapper. Counts measure entries from outside that
    definition, not its internal recursive calls.
    """
    starts = list(re.finditer(r"(?m)^" + re.escape(indent) + r"let (?:rec )?" + re.escape(name) + r"(?=[\s:=(])", source))
    if occurrence >= len(starts):
        raise ValueError("Definition not found: " + name)
    start = starts[occurrence].end()
    if indent:
        end = re.search(r"(?m)^" + re.escape(indent) + r"(?:\(\*\* val |end\b)", source[start:])
    else:
        end = re.search(r"(?m)^(?:let |type |module |open )", source[start:])
    position = start + end.start() if end else len(source)
    # Extracted functor bodies close one space to the left of their declarations.
    if indent:
        closer = re.search(r"(?m)^ end\b", source[start:position])
        if closer:
            position = start + closer.start()
    args = ["measure_arg_" + str(i) for i in range(arity)]
    metric_code = "" if metrics is None else metrics(args)
    wrapper = ("\n" + indent + "let " + name + " " + " ".join(args) + " =\n" + indent +
               '  VplMeasure.region "' + label + '" (fun () ->\n' + metric_code + indent +
               "    " + name + " " + " ".join(args) + ")\n\n")
    return source[:position] + wrapper + source[position:]


def instrument(relative, source):
    if relative == "syntax/SLoopProfile.ml":
        assert source.count("Unix.gettimeofday ()") == 2
        source = source.replace("Unix.gettimeofday ()", "VplMeasure.now ()")
        source = source.replace("let res = f () in", "let res = VplMeasure.stage name f in", 1)
        source = source.replace('"total" total\n', '"total" total;\n  VplMeasure.print ()\n', 1)
    elif relative == "extraction/Canonizer.ml":
        source = wrap(source, "canonize", 1, "integer_tightening", indent="  ", occurrence=1)
        source = wrap(source, "canonize", 1, "canonize", indent="  ",
                      metrics=lambda a: '    VplMeasure.poly "canonize" ' + a[0] + ";\n")
    elif relative == "extraction/PolyTest.ml":
        source = wrap(source, "isBottom", 1, "isBottom", metrics=lambda a: '    VplMeasure.poly "isBottom" ' + a[0] + ";\n")
    elif relative == "extraction/VplInterface.ml":
        pattern = r"    let p2 =\n(      trace DEBUG[\s\S]*? p1)\n    in"
        def debug_region(match):
            return ('    let p2 = if VplMeasure.skip_debug then p1 else\n'
                    '      VplMeasure.region "debug_formatting" (fun () ->\n' + match.group(1) + ')\n    in')
        source, replacements = re.subn(pattern, debug_region, source)
        assert replacements == 2, "Unexpected eager debug-formatting expressions"
        for name, arity, label, indent in [
            ("poly_to_Cs", 1, "vpl_conversion_in", ""),
            ("coq_Cs_to_poly_Q", 1, "vpl_conversion_out", ""),
            ("fromCs_unchecked", 1, "constraint_insertion", "  "),
            ("checkCs", 2, "constraint_certificate_check", "  ")]:
            source = wrap(source, name, arity, label, indent=indent)
    elif relative.endswith("PedraQOracles.ml"):
        for name, arity in [("add", 1), ("isEmpty", 1), ("meet", 1), ("join", 1), ("project", 1), ("projectM", 1)]:
            if re.search(r"(?m)^let " + name + r"[\s:]", source):
                source = wrap(source, name, arity, "oracle_" + name)
    elif relative.endswith("core/Pol.ml"):
        for name, arity in [("addM", 3), ("chkFeasibility", 2), ("logEqSetAddM", 2),
                            ("logrewriteIneqs", 2), ("extract_implicit_eqs", 3),
                            ("logIneqSetAddM", 3), ("project", 3), ("projectM", 3)]:
            source = wrap(source, name, arity, "core_" + name)
    elif relative.endswith("core/Splx.ml"):
        for name, arity in [("mk", 2), ("check", 1)]:
            source = wrap(source, name, arity, "simplex_" + name)
        # Counts only: avoid a timer around every pivot/step.
        source = source.replace("let pivot m xB xN =\n", 'let pivot m xB xN =\n  VplMeasure.bump "simplex.pivots" 1;\n', 1)
    elif relative.startswith("extraction/") and re.search(r"(?m)^ *let validate_two_instrs\b", source):
        from build_pipeline_profiler import wrap_all
        specs = [("validate_two_instrs", 3, "statement_pair"),
                 ("validate_two_instrs_under_guards_integer", 5, "statement_pair_integer"),
                 ("validate_two_accesses", 9, "access_pair"),
                 ("validate_two_accesses_integer", 9, "access_pair_integer"),
                 ("validate_lt_ge_pair", 3, "dependence_query"),
                 ("validate_lt_ge_pair_integer", 3, "dependence_query_integer")]
        for name, arity, label in specs:
            source = wrap_all(source, name, arity, label, measurement_module="VplMeasure")
        # Record same-array pairs separately from early successful array-ID skips.
        source = source.replace("if negb (Pos.eqb id1 id2)\n", 'let () = if Pos.eqb id1 id2 then VplMeasure.bump "access_pairs.same_array" 1 in\n    if negb (Pos.eqb id1 id2)\n')
    elif relative == "extraction/TilingBandScheduleValidator.ml":
        for name, arity in [("make_pluto_band_component_guard_polys", 5),
                            ("make_semantic_band_component_guard_polys", 6),
                            ("make_scalar_aware_band_component_guard_polys", 5)]:
            def dimensions(arguments):
                index = arguments[-2]
                return ('    let rec measure_nat = function Datatypes.O -> 0 | Datatypes.S n -> 1 + measure_nat n in\n'
                        '    VplMeasure.maximum "band.component_index_plus_one" (1 + measure_nat ' + index + ');\n')
            source = wrap(source, name, arity, "band_guard_construction", indent="  ", metrics=dimensions)
    return source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--assets", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--flavor", choices=("vpl", "pipeline", "pipeline-vpl"), default="vpl")
    args = parser.parse_args()
    root = args.source_root.resolve()
    output = args.output.resolve()
    if output.exists():
        raise SystemExit("Use a fresh output directory.")
    output.mkdir(parents=True)
    variables = output / "variables.mk"
    variables.write_text('vpl-profile-variables:\n\t@echo COMPILER $(OCAMLOPT)\n\t@echo OBJECTS $(POLOPT_OBJS)\n\t@echo LIBS $(LIBS) $(LINK_OPT)\n')
    result = subprocess.run(["make", "-s", "-f", "Makefile.extr", "-f", str(variables), "vpl-profile-variables"], cwd=root, text=True, capture_output=True, check=True)
    values = {line.split(" ", 1)[0]: shlex.split(line.split(" ", 1)[1]) for line in result.stdout.splitlines()}
    original_hash = digest(root / "polopt")
    modified = {"syntax/SLoopProfile.ml", "extraction/Canonizer.ml", "extraction/PolyTest.ml",
                "extraction/VplInterface.ml", "extraction/AffineValidator.ml",
                "extraction/TilingBandScheduleValidator.ml", "VPL/ocaml/src/core/Pol.ml",
                "VPL/ocaml/src/core/Splx.ml", "VPL/ocaml/src/coq_ml/PedraQOracles.ml"}
    sources = [(Path(obj).with_suffix(".ml")) for obj in values["OBJECTS"]]
    transform = instrument
    measurement_modules = ["VplMeasure"]
    if args.flavor.startswith("pipeline"):
        from build_pipeline_profiler import instrument as pipeline_transform
        modified = {str(source) for source in sources}
        measurement_modules = ["PipelineMeasure"]
        transform = pipeline_transform
        if args.flavor == "pipeline-vpl":
            measurement_modules = ["VplMeasure", "PipelineMeasure"]
            def transform(relative, source):
                # Actual driver only: do not activate the diagnostic two-pass
                # SLoopProfile route or replace uninstrumented wall measurements.
                result = instrument(relative, source) if relative != "syntax/SLoopProfile.ml" else source
                result = pipeline_transform(relative, result)
                if relative == "syntax/SLoopMain.ml":
                    result = result.replace("  PipelineMeasure.start ();",
                        "  PipelineMeasure.stage_hook := { measure = VplMeasure.stage };\n"
                        "  at_exit VplMeasure.print;\n  PipelineMeasure.start ();", 1)
                return result
    if len({p.name.lower() for p in sources}) != len(sources):
        raise SystemExit("The flat native overlay would have duplicate module names.")
    hashes = {}
    for source in sources:
        original = root / source
        copied = output / source.name
        data = original.read_text()
        transformed = transform(str(source), data) if str(source) in modified else data
        copied.write_text(transformed)
        interface = original.with_suffix(".mli")
        if interface.exists():
            shutil.copy2(interface, output / interface.name)
        compiled_interface = original.with_suffix(".cmi")
        if compiled_interface.exists():
            shutil.copy2(compiled_interface, output / compiled_interface.name)
        hashes[str(source)] = {"original_sha256": digest(original), "overlay_sha256": digest(copied), "instrumented": transformed != data}
    for name in [module + ".ml" for module in measurement_modules] + ["monotonic_clock_stubs.c"]:
        shutil.copy2(args.assets / name, output / name)
    # Search the overlay before the frozen interfaces and native objects.
    compiler = values["COMPILER"][:2] + ["-I", str(output)] + values["COMPILER"][2:]
    commands = []
    log = (output / "build.log").open("w")
    def execute(command):
        commands.append(command)
        log.write(shlex.join(command) + "\n")
        log.flush()
        result = subprocess.run(command, cwd=root, stdout=log, stderr=log)
        if result.returncode:
            raise SystemExit("Build failed; inspect " + str(output / "build.log"))
    for measurement_module in measurement_modules:
        execute(compiler + ["-c", "-o", str(output / (measurement_module + ".cmx")), str(output / (measurement_module + ".ml"))])
    ocaml_include = subprocess.check_output(["ocamlc", "-where"], text=True).strip()
    execute(["cc", "-O2", "-fPIC", "-I", ocaml_include, "-c", "-o",
             str(output / "monotonic_clock_stubs.o"), str(output / "monotonic_clock_stubs.c")])
    for index, source in enumerate(sources):
        interface = output / source.with_suffix(".mli").name
        if interface.exists():
            execute(compiler + ["-c", "-o", str(output / source.with_suffix(".cmi").name), str(interface)])
        execute(compiler + ["-c", "-o", str(output / source.with_suffix(".cmx").name), str(output / source.name)])
        if index % 30 == 0:
            print("Compiled", index + 1, "/", len(sources), flush=True)
    binary = output / ("polopt-profile-" + args.flavor)
    execute(compiler + ["-o", str(binary)] + values["LIBS"] + [str(output / (module + ".cmx")) for module in measurement_modules] +
            [str(output / Path(obj).name) for obj in values["OBJECTS"]] + [str(output / "monotonic_clock_stubs.o")])
    log.close()
    if digest(root / "polopt") != original_hash:
        raise RuntimeError("Original binary changed.")
    for name, row in hashes.items():
        if digest(root / name) != row["original_sha256"]:
            raise RuntimeError("Original source changed: " + name)
    metadata = {"source_root": str(root), "flavor": args.flavor, "original_polopt_sha256": original_hash,
                "ocaml_version": subprocess.check_output(["ocamlc", "-version"], text=True).strip(),
                "instrumented_polopt_sha256": digest(binary), "sources": hashes,
                "measurement_source_sha256": digest(output / (measurement_modules[-1] + ".ml")),
                "measurement_modules_sha256": {module: digest(output / (module + ".ml")) for module in measurement_modules},
                "stub_sha256": digest(output / "monotonic_clock_stubs.c"),
                "commands": commands, "original_binary_and_sources_preserved": True,
                "objects": {p.name: digest(p) for p in output.glob("*.cmx")}}
    metadata["builder_sha256"] = {name: digest(Path(__file__).with_name(name))
                                   for name in ("build_vpl_profiler.py", "build_pipeline_profiler.py")}
    (output / "build-metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps({k: v for k, v in metadata.items() if k not in ("sources", "commands", "objects")}, indent=2))


if __name__ == "__main__":
    main()
