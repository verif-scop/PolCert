#!/usr/bin/env python3
"""Compare generated loop grouping and access order on bounded parameter samples.

This is empirical structural evidence, not a semantic equivalence proof. Loop
variable names and single-iteration wrappers are ignored. A trace records the
remaining loop nesting and iteration counts, plus each statement's ordered
memory-access indices. Arrays are never allocated or read. Truncated samples
are reported as incomplete rather than accepted as full comparisons.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import re
import subprocess
from pathlib import Path

from retention_candidate import select_candidate


HELPERS = r'''
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdint.h>
#include <limits.h>
static uint64_t access_hash=1469598103934665603ULL, shape_hash=1469598103934665603ULL;
static unsigned long long statements=0, events=0, loops=0, parallel_loops=0;
static long long tile[32], tile_min[32], tile_max[32]; static int tile_dimensions=0, tile_capacity=0, tile_seen[32];
static void mix(uint64_t *h, uint64_t x) { *h ^= x; *h *= 1099511628211ULL; }
static void finish(int truncated) {
  printf("%llu %llu %llu %llu %llu %d", (unsigned long long)access_hash,
      (unsigned long long)shape_hash, statements, loops, parallel_loops, truncated);
  for(int i=0;i<tile_capacity;i++) printf(" %lld %lld",tile_min[i],tile_max[i]);
  puts("");
}
static void event(long long tag, long long value) {
  if (++events>2000000) { finish(1); exit(77); }
  mix(&shape_hash,tag); mix(&shape_hash,value);
  if(tag==101) loops++;
  if(tag==102) { loops++; parallel_loops++; }
}
static void record(const char *tag, int n, ...) {
  if (++statements>250000) { finish(1); exit(77); }
  for(const char *p=tag; *p; ++p) { mix(&access_hash,(unsigned char)*p); mix(&shape_hash,(unsigned char)*p); }
  va_list a; va_start(a,n);
  for(int i=0;i<n;i++) { long long v=va_arg(a,long long); mix(&access_hash,v); mix(&shape_hash,v); }
  va_end(a); mix(&access_hash,991); mix(&shape_hash,991);
  mix(&shape_hash,tile_dimensions);
  for(int i=0;i<tile_dimensions;i++) {
    mix(&shape_hash,tile[i]);
    if(!tile_seen[i] || tile[i]<tile_min[i]) tile_min[i]=tile[i];
    if(!tile_seen[i] || tile[i]>tile_max[i]) tile_max[i]=tile[i];
    tile_seen[i]=1;
  }
}
static long long polcert_z_div(long long x,long long y) { if(!y)return 0; long long q=x/y,r=x%y; return q-((r!=0)&&((r<0)!=(y<0))); }
static long long polcert_z_mod(long long x,long long y) { return y?x-y*polcert_z_div(x,y):x; }
#define floord(x,y) polcert_z_div((x),(y))
#define ceild(x,y) (-polcert_z_div(-(x),(y)))
#define min(x,y) ((x)<(y)?(x):(y))
#define max(x,y) ((x)>(y)?(x):(y))
'''


def load_transpiler(source_root):
    path = source_root / "tools/end_to_end_c/loop_to_c.py"
    spec = importlib.util.spec_from_file_location("retention_loop_to_c", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def access_statement(text, ignored_identifiers=()):
    """Trace ordered explicit memory addresses, not arithmetic pretty-printing."""
    indices = []
    pieces = []
    cursor = 0
    while cursor < len(text):
        if text[cursor] != "[":
            pieces.append(text[cursor])
            cursor += 1
            continue
        depth = 1
        end = cursor + 1
        while end < len(text) and depth:
            depth += (text[end] == "[") - (text[end] == "]")
            end += 1
        if depth:
            raise ValueError("Unbalanced array subscript")
        indices.append(text[cursor + 1:end - 1])
        pieces.append("[]")
        cursor = end
    abstract = "".join(pieces)
    left, right = abstract.split("=", 1)
    written = re.search(r"([A-Za-z_][\w]*)(\[\])*", left)
    if written is None:
        raise ValueError("Unsupported assignment target: " + text)
    tag = "W:" + re.sub(r"\s", "", left)
    ignored = set(ignored_identifiers) | {"true", "false"}
    for match in re.finditer(r"(?<![\w$])([A-Za-z_$][\w$]*)((?:\[\])*)", right):
        name, subscripts = match.groups()
        tail = right[match.end():].lstrip()
        if subscripts:
            tag += ";R:" + name + subscripts
        elif tail.startswith("("):
            tag += ";F:" + name
        elif name not in ignored:
            tag += ";R:" + name
    args = "".join(", (long long)(" + expr + ")" for expr in indices)
    return "record(" + json.dumps(tag) + ", " + str(len(indices)) + args + ");"


def instrument(text, tile_variables=None, statement_tile_counts=None, parameters=()):
    output = []
    stack = []
    next_loop = 0
    parallel = False
    loop_variables = []
    macro_tags = {}
    is_pluto = "Start of CLooG code" in text or bool(re.search(r"#define\s+S\d+", text))

    def assign_tile_prefix(tag):
        count = (statement_tile_counts or {}).get(tag, 0)
        variables = [var for var, singleton in loop_variables if not singleton]
        if len(variables) < count:
            raise ValueError("Fewer enclosing loops than varying tile dimensions for " + tag)
        return "tile_dimensions={}; ".format(count) + " ".join(
            "tile[{}]={};".format(index, var) for index, var in enumerate(variables[:count]))

    for line in text.splitlines():
        stripped = line.strip()
        macro = re.match(r"(#define\s+S\d+\([^)]*\))\s*(.+)$", stripped)
        if macro:
            macro_parameters = macro.group(1).split("(", 1)[1].rstrip(")").split(",")
            statement = access_statement(macro.group(2), [*parameters, *macro_parameters])
            macro_tags[re.search(r"S\d+", macro.group(1)).group()] = json.loads(statement.split("record(", 1)[1].split(", ", 1)[0])
            output.append(macro.group(1) + " " + statement)
            continue
        if stripped.startswith("#pragma omp parallel"):
            parallel = True
            continue
        if stripped.startswith("#pragma"):
            continue
        loop = re.match(r"for\s*\((.+);\s*(.+);\s*(.+)\)\s*\{\s*$", stripped)
        if loop:
            init, condition, increment = loop.groups()
            assign = re.match(r"(?:(?:long long|int)\s+)?([\w$]+)\s*=\s*(.+)$", init)
            if not assign:
                raise ValueError("Unsupported loop init: " + line)
            var, lower = assign.groups()
            test = re.match(re.escape(var) + r"\s*(<=|<|>=|>)\s*(.+)$", condition)
            if not test:
                raise ValueError("Unsupported loop test: " + line)
            operator, upper = test.groups()
            if increment.replace(" ", "") not in {var + "++", "++" + var, var + "--", "--" + var}:
                raise ValueError("Unsupported loop increment: " + line)
            descending = "--" in increment
            count = "({})-({}){}".format(lower if descending else upper,
                        upper if descending else lower, "+1" if "=" in operator else "")
            number = next_loop
            next_loop += 1
            output.append("{{ long long n{0}=({1}); int active{0}=(n{0}>1);".format(number, count))
            if tile_variables is None:
                output.append("if(active{0}) event({1},n{0});".format(number, 102 if parallel else 101))
            output.append(line)
            try:
                constant_count = int(upper) - int(lower) + (1 if operator == "<=" else 0)
            except ValueError:
                constant_count = None
            loop_variables.append((var, constant_count == 1))
            if tile_variables is None:
                output.append("if(active{0}) event(103,0);".format(number))
            elif var in tile_variables:
                output.append("tile[{}]={};".format(tile_variables.index(var), var))
            if tile_variables is not None and parallel:
                output.append("if(active{}) parallel_loops++;".format(number))
            stack.append(("loop", number))
            parallel = False
            continue
        if stripped == "}":
            if not stack:
                raise ValueError("Unbalanced closing brace")
            kind, number = stack.pop()
            if kind == "loop":
                loop_variables.pop()
                if tile_variables is None:
                    output.append("if(active{0}) event(104,0); }} if(active{0}) event(105,0); }}".format(number))
                else:
                    output.append("} }")
            else:
                output.append(line)
            continue
        if stripped.endswith("{"):
            stack.append(("other", None))
        call = re.match(r"(S\d+)\(", stripped)
        if call and statement_tile_counts is not None:
            output.append(assign_tile_prefix(macro_tags[call.group(1)]))
        if stripped.endswith(";") and "=" in stripped and not stripped.startswith(("for", "int ", "long long ", "register ")):
            if is_pluto:
                output.append(line)
            else:
                statement = access_statement(stripped, [*parameters, *(var for var, _ in loop_variables)])
                if statement_tile_counts is not None:
                    output.append(assign_tile_prefix(json.loads(statement.split("record(", 1)[1].split(", ", 1)[0])))
                output.append(statement)
        else:
            output.append(line)
    if stack:
        raise ValueError("Unclosed block")
    return "\n".join(output)


def params_from_loop(text):
    match = re.search(r"context\(([^)]*)\)", text)
    return [name.strip() for name in match.group(1).split(",") if name.strip()] if match else []


def build_trace(body, params, target, tile_count=0):
    definitions = []
    executable = []
    for line in body.splitlines():
        (definitions if line.lstrip().startswith("#define") else executable).append(line)
    declarations = "\n".join("long long {}=argc>{}?atoll(argv[{}]):5;".format(name, i + 1, i + 1)
                             for i, name in enumerate(params))
    source = HELPERS + "\n" + "\n".join(definitions) + "\nint main(int argc,char**argv){\ntile_capacity=tile_dimensions=" + str(tile_count) + ";\n" + declarations + "\n" + "\n".join(executable) + "\nfinish(0); return 0;\n}\n"
    target.with_suffix(".c").write_text(source)
    compiled = subprocess.run(["gcc", "-std=gnu11", "-O0", "-w", str(target.with_suffix(".c")), "-o", str(target)],
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=15)
    if compiled.returncode:
        return {"status": "compile-error", "stderr": compiled.stderr}
    return {"status": "ok"}


def execute_trace(executable, sample):
    try:
        result = subprocess.run([str(executable), *map(str, sample)], capture_output=True, text=True, timeout=3)
    except subprocess.TimeoutExpired:
        return {"status": "timeout"}
    try:
        values = list(map(int, result.stdout.split()))
        access_hash, shape_hash, statements, loops, par, truncated = values[:6]
    except ValueError:
        return {"status": "execution-error", "stdout": result.stdout, "stderr": result.stderr}
    return {"status": "truncated" if truncated else "ok", "access_hash": access_hash,
            "shape_hash": shape_hash, "statements": statements, "loops": loops, "parallel_loops": par,
            "tile_coordinate_ranges": [values[i:i+2] for i in range(6,len(values),2)]}


def compare_case(case_dir, source_root, tile_rows=None, canonical_rows=None, geometry=None,
                 producer_file=None, producer_sha256=None):
    result = json.loads((case_dir / "result.json").read_text())
    final = (case_dir / "polcert.stdout.txt").read_text()
    if result["returncode"] or "== Optimized Loop ==" not in final:
        return {"status": "no-final-loop"}
    final = final.split("== Optimized Loop ==", 1)[1].strip()
    source_path = case_dir / 'source.loop'
    source_loop = (source_path if source_path.exists() else Path(result["loop_input"])).read_text()
    selection = select_candidate(case_dir, explicit=producer_file, expected_sha256=producer_sha256)
    if selection['status'] != 'selected':
        return {"status": selection['status'], "producer_selection": selection}
    selected_producer = Path(selection['selected']['file'])
    producer = selected_producer.read_text()
    target = case_dir / "trace"
    target.mkdir(exist_ok=True)
    params = params_from_loop(final)
    pluto_tiles = ["t" + str(row + 1) for row in tile_rows] if tile_rows is not None else None
    polcert_tiles = ["i" + str(canonical_rows.index(row)) for row in tile_rows] if tile_rows is not None else None
    statement_tile_counts = None
    if geometry:
        counts = {row["statement"] + 1: sum(coordinate["varies"] is True and coordinate["scheduled"]
                                           for coordinate in row["coordinates"])
                  for row in geometry["statements"]}
        statement_tile_counts = {}
        for match in re.finditer(r"^#define\s+S(\d+)\(([^)]*)\)\s*(.+)$", producer, re.MULTILINE):
            tag = json.loads(access_statement(match.group(3), [*params, *match.group(2).split(",")]).split("record(", 1)[1].split(", ", 1)[0])
            number = counts.get(int(match.group(1)), 0)
            if tag in statement_tile_counts and statement_tile_counts[tag] != number:
                return {"status": "ambiguous-statement-tiling"}
            statement_tile_counts[tag] = number
    try:
        transpiler = load_transpiler(source_root)
        polcert = instrument(transpiler.transpile_loop_text(final), polcert_tiles, statement_tile_counts, params)
        pluto = instrument(producer, pluto_tiles, statement_tile_counts, params)
        original = instrument(transpiler.transpile_loop_text(source_loop), [], parameters=params)
    except (ValueError, SyntaxError) as exc:
        return {"status": "unsupported-syntax", "detail": str(exc)}
    built = {}
    for name, body in [("pluto", pluto), ("polcert", polcert), ("source", original)]:
        built[name] = build_trace(body, params, target / name, len(tile_rows or []) if name != "source" else 0)
    if any(info["status"] != "ok" for info in built.values()):
        return {"status": "compile-error", "builds": built}
    # Isolate one large axis per sample to cross tile boundaries without an
    # exponential full-size domain in high-dimensional kernels.
    samples = [[5] * len(params)]
    for i in range(min(len(params), 6)):
        for extent, other_extent in [(37, 3), (259, 1), (259, 2)]:
            sample = [other_extent] * len(params)
            sample[i] = extent
            samples.append(sample)
    observations = []
    for sample in samples:
        left, right = (execute_trace(target / name, sample) for name in ["pluto", "polcert"])
        source_trace = execute_trace(target / "source", sample)
        complete = left["status"] == right["status"] == "ok"
        observations.append({"parameters": dict(zip(params, sample)), "pluto": left, "polcert": right, "source": source_trace,
            "access_match": complete and left["statements"] == right["statements"] and left["access_hash"] == right["access_hash"],
            "shape_match": complete and left["shape_hash"] == right["shape_hash"]})
    complete = [row for row in observations if row["pluto"]["status"] == row["polcert"]["status"] == "ok"
                and row["pluto"]["statements"] > 0]
    return {"status": "compared", "producer_file": str(selected_producer),
            "producer_selection": selection,
            "statement_tile_counts": statement_tile_counts,
            "shape_mode": "statement-specific outer tile groups" if statement_tile_counts is not None else
                          "tile-coordinate groups" if tile_rows is not None else "all non-singleton loops",
            "pluto_tile_variables": None if statement_tile_counts is not None else pluto_tiles,
            "polcert_tile_variables": None if statement_tile_counts is not None else polcert_tiles,
            "complete_nonempty_samples": len(complete),
            "incomplete_samples": sum(row["pluto"]["status"] != "ok" or row["polcert"]["status"] != "ok" for row in observations),
            "varying_tile_coordinates": [index for index in range(len(tile_rows or []))
                if any(row["pluto"]["tile_coordinate_ranges"][index][0] != row["pluto"]["tile_coordinate_ranges"][index][1] for row in complete)],
            "producer_changes_source_order": any(row["source"]["status"] == row["pluto"]["status"] == "ok"
                and row["source"]["statements"] == row["pluto"]["statements"]
                and row["source"]["access_hash"] != row["pluto"]["access_hash"] for row in observations),
            "access_match": bool(complete) and all(row["access_match"] for row in complete),
            "shape_match": bool(complete) and all(row["shape_match"] for row in complete),
            "observations": observations}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case_dir", type=Path)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--tile-rows", type=int, nargs="+")
    parser.add_argument("--canonical-rows", type=int, nargs="+")
    args = parser.parse_args()
    result = compare_case(args.case_dir, args.source_root, args.tile_rows, args.canonical_rows)
    (args.case_dir / "trace-comparison.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key != "observations"}, indent=2))


if __name__ == "__main__":
    main()
