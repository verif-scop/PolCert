#!/usr/bin/env python3
"""Describe effects in captured Pluto proposals, independently of acceptance.

This is experimental evidence analysis, not a verified validator. Schedule
comparisons remove coordinates common to the whole program and common positive
scaling. Tiling requires paired floor constraints and a coordinate that can vary
within one parameter instance. No effect is inferred from a requested flag.
"""
from __future__ import annotations

import argparse
import ctypes
import ctypes.util
from dataclasses import dataclass, field
from fractions import Fraction
import json
import hashlib
from math import gcd
from pathlib import Path
import re

from retention_candidate import select_candidate


_ORDER_CACHE = {}


class ScopError(ValueError):
    pass


@dataclass
class Relation:
    kind: str
    outputs: int
    inputs: int
    locals: int
    parameters: int
    rows: list


@dataclass
class Statement:
    domain: Relation
    scattering: Relation | None = None
    accesses: list = field(default_factory=list)


@dataclass
class Scop:
    statements: list
    context: Relation
    path: str = ""


def parse_scop(text, path=""):
    """Parse relation matrices; unsupported or malformed relations fail closed."""
    if text.count("<OpenScop>") != 1 or "</OpenScop>" not in text:
        raise ScopError("expected one complete OpenScop object")
    lines = [line.split("#", 1)[0].strip() for line in text.splitlines()]
    lines = [line for line in lines if line]
    kinds = {"CONTEXT", "DOMAIN", "SCATTERING", "READ", "WRITE", "MAYWRITE"}
    statements, context = [], None
    index = 0
    while index < len(lines):
        kind = lines[index]
        if kind not in kinds:
            index += 1
            continue
        try:
            header = [int(token) for token in lines[index + 1].split()]
            if len(header) != 6:
                raise ScopError("relation header must have six integers")
            count, columns, outputs, inputs, locals_, parameters = header
            if min(header) < 0 or columns != outputs + inputs + locals_ + parameters + 2:
                raise ScopError("inconsistent relation dimensions")
            rows = [[int(token) for token in line.split()]
                    for line in lines[index + 2:index + 2 + count]]
            if len(rows) != count or any(len(row) != columns or row[0] not in (0, 1) for row in rows):
                raise ScopError("incomplete or malformed relation rows")
        except (IndexError, ValueError) as error:
            raise ScopError("{}: {}".format(kind, error)) from error
        relation = Relation(kind, outputs, inputs, locals_, parameters, rows)
        index += count + 2
        if kind == "CONTEXT":
            if context is not None:
                raise ScopError("multiple contexts")
            context = relation
        elif kind == "DOMAIN":
            statements.append(Statement(relation))
        elif not statements:
            raise ScopError("statement relation precedes domain")
        elif kind == "SCATTERING":
            if statements[-1].scattering is not None:
                raise ScopError("multiple scattering relations in one statement")
            statements[-1].scattering = relation
        else:
            statements[-1].accesses.append(relation)
    if context is None or any(stmt.scattering is None for stmt in statements):
        raise ScopError("missing context or scattering")
    for stmt in statements:
        if stmt.domain.inputs or stmt.scattering.inputs != stmt.domain.outputs:
            raise ScopError("domain/scattering dimensions disagree")
        if stmt.domain.parameters != context.parameters:
            raise ScopError("parameter counts disagree")
    return Scop(statements, context, str(path))


def read_scop(path):
    return parse_scop(Path(path).read_text(), path)


def affine_map(relation):
    """Solve equalities as outputs = coefficients * (inputs, parameters, 1)."""
    if relation.locals or any(row[0] != 0 for row in relation.rows):
        raise ScopError("relation is not an explicit affine map")
    n = relation.outputs
    matrix = [[Fraction(v) for v in row[1:]] for row in relation.rows]
    pivot = 0
    for column in range(n):
        selected = next((r for r in range(pivot, len(matrix)) if matrix[r][column]), None)
        if selected is None:
            raise ScopError("affine map has an undetermined output")
        matrix[pivot], matrix[selected] = matrix[selected], matrix[pivot]
        factor = matrix[pivot][column]
        matrix[pivot] = [v / factor for v in matrix[pivot]]
        for r in range(len(matrix)):
            if r != pivot:
                factor = matrix[r][column]
                matrix[r] = [v - factor * p for v, p in zip(matrix[r], matrix[pivot])]
        pivot += 1
    if any(any(row) for row in matrix[n:]):
        raise ScopError("map has additional input restrictions")
    return [tuple(-v for v in row[n:]) for row in matrix[:n]]


def padded_maps(scop):
    maps = [affine_map(stmt.scattering) for stmt in scop.statements]
    width = max((len(rows) for rows in maps), default=0)
    return [rows + [tuple(Fraction(0) for _ in range(stmt.domain.outputs + stmt.domain.parameters + 1))]
            * (width - len(rows)) for rows, stmt in zip(maps, scop.statements)]


def canonical_schedule(scop):
    """Return schedule expressions and retained zero-based scattering rows.

    Only whole-program constant/parameter coordinates are removed. Statement-
    specific constants remain because they can encode statement order.
    """
    maps = padded_maps(scop)
    if not maps:
        return [], []
    width = len(maps[0])
    kept, normalized = [], [[] for _ in maps]
    for dimension in range(width):
        expressions = [rows[dimension] for rows in maps]
        suffixes = [expr[stmt.domain.outputs:] for expr, stmt in zip(expressions, scop.statements)]
        if all(not any(expr[:stmt.domain.outputs]) for expr, stmt in zip(expressions, scop.statements)) and len(set(suffixes)) == 1:
            continue
        kept.append(dimension)
        # Shared parameter offsets and constants do not change relative order.
        common = suffixes[0]
        shifted = [tuple(expr[:stmt.domain.outputs]) + tuple(v - offset for v, offset in zip(suffix, common))
                   for expr, stmt, suffix in zip(expressions, scop.statements, suffixes)]
        denominator = 1
        for expr in shifted:
            for value in expr:
                denominator = denominator * value.denominator // gcd(denominator, value.denominator)
        factor = 0
        for expr in shifted:
            for value in expr:
                factor = gcd(factor, abs(int(value * denominator)))
        scale = Fraction(factor, denominator) if factor else Fraction(1)
        for target, expr in zip(normalized, shifted):
            target.append(tuple(v / scale for v in expr))
    return normalized, kept


def schedule_change(before, after):
    if len(before.statements) != len(after.statements):
        return None
    if any(a.domain.outputs != b.domain.outputs for a, b in zip(before.statements, after.statements)):
        return None
    return canonical_schedule(before)[0] != canonical_schedule(after)[0]


def compiler_kept_rows(scop):
    """Mirror PolyLang's zero-row mask, not the stronger comparison normalizer."""
    maps = [affine_map(stmt.scattering) for stmt in scop.statements]
    width = max((len(rows) for rows in maps), default=0)
    return [dimension for dimension in range(width)
            if any(dimension < len(rows) and any(rows[dimension]) for rows in maps)]


def _linear(coefficients, names):
    terms = ["{}*{}".format(c, name) for c, name in zip(coefficients[:-1], names) if c]
    if coefficients[-1] or not terms:
        terms.append(str(coefficients[-1]))
    return " + ".join(terms)


def _constraints(relation, names):
    if relation.locals:
        raise ScopError("local existential dimensions are unsupported")
    return ["({}) {} 0".format(_linear(row[1:], names), "=" if row[0] == 0 else ">=") for row in relation.rows]


def isl_nonempty(description):
    """Use the already installed ISL library; unavailable/error means unknown."""
    name = ctypes.util.find_library("isl")
    if name is None:
        return None
    try:
        lib = ctypes.CDLL(name)
        lib.isl_ctx_alloc.restype = ctypes.c_void_p
        lib.isl_ctx_free.argtypes = [ctypes.c_void_p]
        lib.isl_set_read_from_str.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
        lib.isl_set_read_from_str.restype = ctypes.c_void_p
        lib.isl_set_is_empty.argtypes = [ctypes.c_void_p]
        lib.isl_set_is_empty.restype = ctypes.c_int
        lib.isl_set_free.argtypes = [ctypes.c_void_p]
        context = lib.isl_ctx_alloc()
        if hasattr(lib, "isl_ctx_set_max_operations"):
            lib.isl_ctx_set_max_operations.argtypes = [ctypes.c_void_p, ctypes.c_ulong]
            lib.isl_ctx_set_max_operations(context, 100000)
        value = None
        try:
            value = lib.isl_set_read_from_str(context, description.encode())
            if not value:
                return None
            empty = lib.isl_set_is_empty(value)
            return None if empty < 0 else not bool(empty)
        finally:
            if value:
                lib.isl_set_free(value)
            lib.isl_ctx_free(context)
    except (AttributeError, OSError):
        return None


def _difference(left, right, xs, ys, params):
    coefficients = {}
    constant = left[-1] - right[-1]
    for value, name in zip(left[:-1], xs + params):
        coefficients[name] = coefficients.get(name, Fraction(0)) + value
    for value, name in zip(right[:-1], ys + params):
        coefficients[name] = coefficients.get(name, Fraction(0)) - value
    names = list(coefficients)
    values = [coefficients[name] for name in names] + [constant]
    denominator = 1
    for value in values:
        denominator = denominator * value.denominator // gcd(denominator, value.denominator)
    return _linear([int(v * denominator) for v in values], names)


def _lex_less(left, right, xs, ys, params):
    if len(left) != len(right):
        raise ScopError("lexicographic schedules have unequal widths")
    alternatives, equalities = [], []
    for a, b in zip(left, right):
        difference = _difference(a, b, xs, ys, params)
        alternatives.append("(" + " and ".join(equalities + ["({}) <= -1".format(difference)]) + ")")
        equalities.append("({}) = 0".format(difference))
    return "(" + " or ".join(alternatives) + ")" if alternatives else "0 = 1"


def order_change(before, after, pair_budget=32):
    """Look for a reversed instance pair; cap both pair and ISL-operation costs.

    Absence of a reversed pair does not imply absence of an affine effect:
    skewing can change loop coordinates while preserving lexicographic order.
    """
    changed = schedule_change(before, after)
    if changed is False:
        return {"status": "absent", "queries": 0, "reason": "equivalent normalized schedules"}
    if changed is None:
        return {"status": "unknown", "queries": 0, "reason": "statement correspondence or dimension changed"}
    material = repr((before.context, before.statements, after.context, after.statements, pair_budget))
    key = hashlib.sha256(material.encode()).hexdigest()
    if key in _ORDER_CACHE:
        return dict(_ORDER_CACHE[key], cached=True)
    for old, new in zip(before.statements, after.statements):
        if [(a.kind, affine_map(a)) for a in old.accesses] != [(a.kind, affine_map(a)) for a in new.accesses]:
            return {"status": "unknown", "queries": 0, "reason": "access-based statement correspondence differs"}
    old_maps = padded_maps(before)
    new_maps = padded_maps(after)
    n = len(before.statements)
    pairs = [(i, i) for i in range(n)] + [(i, j) for i in range(n) for j in range(n) if i != j]
    params = ["p{}".format(i) for i in range(before.context.parameters)]
    queries, inconclusive = 0, False
    answer = None
    for left, right in pairs[:pair_budget]:
        xs = ["x{}".format(i) for i in range(before.statements[left].domain.outputs)]
        ys = ["y{}".format(i) for i in range(before.statements[right].domain.outputs)]
        constraints = _constraints(before.context, params) + _constraints(after.context, params)
        for scop in (before, after):
            constraints.extend(_constraints(scop.statements[left].domain, xs + params))
            constraints.extend(_constraints(scop.statements[right].domain, ys + params))
        constraints += [_lex_less(old_maps[left], old_maps[right], xs, ys, params),
                        _lex_less(new_maps[right], new_maps[left], ys, xs, params)]
        description = "[{}] -> {{ [{}] : {} }}".format(",".join(params), ",".join(xs + ys), " and ".join(constraints))
        possible = isl_nonempty(description)
        queries += 1
        if possible:
            answer = {"status": "observed", "queries": queries, "statement_pair": [left, right],
                      "witness_query": description, "reason": "a feasible instance pair changes execution order"}
            break
        inconclusive = inconclusive or possible is None
    if answer is None:
        answer = {"status": "unknown" if inconclusive or len(pairs) > pair_budget else "absent", "queries": queries,
                  "reason": "query budget/error" if inconclusive or len(pairs) > pair_budget else "no reversed pair; coordinate/loop-bound changes remain possible"}
    answer["pair_budget"] = pair_budget
    answer["isl_operation_budget_per_query"] = 100000
    if len(_ORDER_CACHE) >= 512:
        _ORDER_CACHE.clear()
    _ORDER_CACHE[key] = answer
    return answer


def coordinate_varies(scop, statement, dimension):
    """Can two instances share parameters but have distinct tile coordinates?"""
    domain = statement.domain
    params = ["p{}".format(i) for i in range(domain.parameters)]
    xs = ["x{}".format(i) for i in range(domain.outputs)]
    ys = ["y{}".format(i) for i in range(domain.outputs)]
    constraints = (_constraints(scop.context, params) + _constraints(domain, xs + params)
                   + _constraints(domain, ys + params) + ["{} + 1 <= {}".format(xs[dimension], ys[dimension])])
    description = "[{}] -> {{ [{}] : {} }}".format(",".join(params), ",".join(xs + ys), " and ".join(constraints))
    return isl_nonempty(description)


def floor_coordinates(before, after):
    """Find newly introduced q with B*q <= f < B*q+B in domain rows."""
    if len(before.statements) != len(after.statements):
        raise ScopError("tiling-stage statement count changed")
    details = []
    for statement_id, (old, new) in enumerate(zip(before.statements, after.statements)):
        added = new.domain.outputs - old.domain.outputs
        if added < 0:
            raise ScopError("tiling removed domain dimensions")
        if new.domain.locals:
            raise ScopError("tiling uses local existential dimensions")
        schedule = affine_map(new.scattering)
        tile_rows = [r for r, expr in enumerate(schedule)
                     if any(expr[:added]) and not any(expr[added:new.domain.outputs])]
        found = []
        for dimension in range(added):
            candidates = []
            for lower in new.domain.rows:
                size = -lower[dimension + 1]
                if lower[0] != 1 or size < 2:
                    continue
                rest = lower[1:-1]
                for upper in new.domain.rows:
                    if upper[0] == 1 and upper[1:-1] == [-v for v in rest] and lower[-1] + upper[-1] == size - 1:
                        numerator = lower[1:]
                        numerator = numerator[:dimension] + [0] + numerator[dimension + 1:]
                        if not any(numerator[:-1]):
                            continue
                        candidates.append({"dimension": dimension, "size": size, "numerator": numerator,
                                           "parents": [i for i, value in enumerate(numerator[:added]) if value]})
            if len(candidates) == 1:
                candidate = candidates[0]
                candidate["varies"] = coordinate_varies(after, new, dimension)
                candidate["scheduled"] = any(expr[dimension] for expr in schedule)
                found.append(candidate)
        by_dim = {row["dimension"]: row for row in found}

        def depth(dimension, visiting):
            if dimension in visiting or dimension not in by_dim:
                return None
            parents = by_dim[dimension]["parents"]
            if not parents:
                return 1
            depths = [depth(parent, visiting | {dimension}) for parent in parents]
            return None if any(d is None for d in depths) else 1 + max(depths)

        for row in found:
            row["level"] = depth(row["dimension"], set())
        details.append({"statement": statement_id, "added_tile_dimensions": added,
                        "matched_tile_dimensions": len(found), "tile_schedule_rows": tile_rows,
                        "coordinates": found})
    return details


def _effect(status, evidence=None, **details):
    return {"status": status, "evidence": evidence or [], "details": details}


def iss_debug_statement_count(text):
    """Count complete statement records in Pluto's immediate After ISS dump.

    Later driver phases can discard a split proposal. Their input therefore
    cannot be used as the only evidence of what the producer actually proposed.
    """
    marker = re.search(r"^After ISS\s*$", text, re.MULTILINE)
    if marker is None:
        return None
    section = re.split(r"^(?:--- Dep \d|\[pluto\]|After ISS\s*$)",
                       text[marker.end():], maxsplit=1, flags=re.MULTILINE)[0]
    headers = list(re.finditer(r'^S(\d+)\s+"', section, re.MULTILINE))
    ids = [int(header.group(1)) for header in headers]
    if not ids or ids != list(range(1, len(ids) + 1)):
        return None
    for index, header in enumerate(headers):
        end = headers[index + 1].start() if index + 1 < len(headers) else len(section)
        record = section[header.end():end]
        if "Index set" not in record or not re.search(r"^T\(S{}\):".format(ids[index]), record, re.MULTILINE):
            return None
    return len(ids)


def analyze_producer(case_dir):
    """Analyze captured optimizer output. This function never reads acceptance."""
    case_dir = Path(case_dir)
    effects = {name: _effect("unknown") for name in
               ("affine", "iss", "rectangular_tiling", "two_level_tiling", "diamond_tiling", "parallelization")}
    result = {"schema_version": 1, "effects": effects, "tile_sizes": [], "stages": [],
              "final_geometry": {}, "errors": []}
    from retention_baseline import producer_case_root
    independent = producer_case_root(case_dir) != case_dir
    if independent:
        selection = select_candidate(case_dir)
        result['producer_selection'] = selection
        if selection['status'] != 'selected':
            result['errors'].append(selection['status'])
            return result
    invocations = sorted((producer_case_root(case_dir) / "pluto").glob("*/invocation.json"), key=lambda p: int(p.parent.name))
    if not invocations:
        result["errors"].append("no completed captured Pluto invocation")
        return result
    affine_observed, affine_unknown, split_observed, split_unknown = [], [], [], []
    order_checks = []
    tiled_stages = []
    stdout_all = []
    complete = True
    final = final_base = None
    captured_outputs = []
    pending_bridge = None
    iss_debug_records = []
    schedule_metadata_missing = False
    for invocation_path in invocations:
        folder = invocation_path.parent
        try:
            invocation = json.loads(invocation_path.read_text())
            if invocation.get("input") is None and not (folder / "input.scop").exists():
                # The driver also invokes Pluto for capability/help queries.
                continue
            complete = complete and invocation.get("returncode") == 0
            text = (folder / "stdout.txt").read_text(errors="replace") if (folder / "stdout.txt").exists() else ""
            stdout_all.append(text)
            paths = {"input": folder / "input.scop"}
            paths.update({name: folder / ("output." + suffix + ".scop") for name, suffix in
                          (("before", "beforescheduling"), ("mid", "midtransform"), ("post", "posttile"), ("after", "afterscheduling"))})
            scops = {name: read_scop(path) for name, path in paths.items() if path.exists()}
            if pending_bridge is not None and "input" in scops:
                bridge_source, debug_record = pending_bridge
                old_count = len(bridge_source.statements)
                new_count = len(scops["input"].statements)
                if debug_record is not None:
                    debug_record["next_optimizer_statements"] = new_count
                    debug_record["next_optimizer_input"] = scops["input"].path
                if new_count > old_count:
                    split_observed.append({"before": old_count, "after": new_count,
                        "files": [bridge_source.path, scops["input"].path],
                        "phase": "ISS proposal recovered from debug output and submitted to the next optimizer phase"})
                elif new_count < old_count:
                    split_unknown.append("ISS bridge statement count decreased")
                pending_bridge = None
            debug_record = None
            if "input" in scops and "--iss" in invocation.get("argv", []):
                debug_count = iss_debug_statement_count(text)
                if debug_count is not None:
                    old_count = len(scops["input"].statements)
                    debug_record = {"before": old_count, "after": debug_count,
                        "files": [scops["input"].path, str(folder / "stdout.txt")],
                        "phase": "immediate After ISS producer dump; independent of subsequent driver import"}
                    iss_debug_records.append(debug_record)
                    if debug_count > old_count:
                        split_observed.append(debug_record)
                    elif debug_count < old_count:
                        split_unknown.append("immediate After ISS statement count decreased")
            if "input" in scops and "after" not in scops and "--iss" in invocation.get("argv", []) and "--moredebug" in invocation.get("argv", []):
                if independent:
                    # This is the whole independent ISS compilation, not a
                    # prefetch that should feed another captured invocation.
                    c_file = folder / 'output.pluto.c'
                    pragmas = re.findall(r'^\s*#pragma\s+omp\s+parallel\s+for\b.*$',
                                         c_file.read_text(), re.MULTILINE)
                    captured_outputs.append((c_file, None, None, pragmas))
                    schedule_metadata_missing = True
                    if debug_record is None:
                        split_unknown.append('independent ISS baseline has no complete After ISS record')
                    result['stages'].append({'invocation': str(invocation_path),
                        'files': {'input': scops['input'].path, 'debug': str(folder / 'stdout.txt')},
                        'statement_counts': {'input': len(scops['input'].statements)},
                        'mode': 'independent ISS debug output without --dumpscop'})
                    continue
                # This established driver route requests a debug-format ISS
                # proposal, not --dumpscop. Track the next input separately:
                # it need not retain the actual producer-side split.
                pending_bridge = (scops["input"], debug_record)
                continue
            if "input" not in scops or "after" not in scops:
                raise ScopError("missing input or final proposal")
            final = scops["after"]
            final_base = scops.get("mid", scops["input"])
            c_file = folder / "output.pluto.c"
            pragmas = (re.findall(r"^\s*#pragma\s+omp\s+parallel\s+for\b.*$", c_file.read_text(), re.MULTILINE)
                       if c_file.exists() else [])
            captured_outputs.append((c_file, final, final_base, pragmas))
            record = {"invocation": str(invocation_path), "files": {name: scop.path for name, scop in scops.items()},
                      "statement_counts": {name: len(scop.statements) for name, scop in scops.items()}}
            result["stages"].append(record)
            affine_pairs = [(scops["input"], scops.get("mid", scops["after"]))]
            if "post" in scops:
                affine_pairs.append((scops["post"], scops["after"]))
            for before, after in affine_pairs:
                changed = schedule_change(before, after)
                if changed is True:
                    affine_observed.append([before.path, after.path])
                    order_checks.append({"files": [before.path, after.path], **order_change(before, after)})
                elif changed is None:
                    affine_unknown.append([before.path, after.path])
            split_after = scops.get("mid", scops["after"])
            old_count, new_count = len(scops["input"].statements), len(split_after.statements)
            if new_count > old_count:
                split_observed.append({"before": old_count, "after": new_count,
                                       "files": [scops["input"].path, split_after.path]})
            elif new_count < old_count:
                split_unknown.append("statement count decreased")
            if "post" in scops:
                tiles = floor_coordinates(scops.get("mid", scops["input"]), scops["post"])
                tiled_stages.append({"files": [scops.get("mid", scops["input"]).path, scops["post"].path], "statements": tiles})
        except (ScopError, OSError, ValueError) as error:
            complete = False
            result["errors"].append("{}: {}".format(folder, error))
    if pending_bridge is not None:
        split_unknown.append("ISS debug proposal lacks a subsequent captured input")
    reversed_order = any(check["status"] == "observed" for check in order_checks)
    effects["affine"] = _effect("observed" if reversed_order else "unknown" if affine_observed or affine_unknown or not complete or schedule_metadata_missing else "absent",
                                 affine_observed, normalized_schedule_changed=bool(affine_observed),
                                 iteration_order_checks=order_checks,
                                 comparison="Observed requires a feasible order-reversed pair. Changed coordinates without reordering require final-loop structural evidence.")
    effects["iss"] = _effect("observed" if split_observed else "unknown" if split_unknown or not complete else "absent",
                              split_observed, debug_statement_counts=iss_debug_records,
                              comparison="statement-count increase in the immediate ISS proposal or before tiling; neither final-loop retention nor partition correctness is established by this analysis")
    coordinates = [coordinate for stage in tiled_stages for stmt in stage["statements"] for coordinate in stmt["coordinates"]]
    result["tile_sizes"] = sorted({row["size"] for row in coordinates})
    varying = [row for row in coordinates if row["varies"] is True and row["scheduled"]]
    tile_unknown = (not complete or schedule_metadata_missing or any(row["varies"] is None for row in coordinates)
                    or any(stmt["added_tile_dimensions"] != stmt["matched_tile_dimensions"]
                           for stage in tiled_stages for stmt in stage["statements"]))
    tiled_status = "observed" if varying else "unknown" if tile_unknown else "absent"
    text = "\n".join(stdout_all)
    diamond_message = "Concurrent start hyperplanes found" in text
    diamond_status = ("observed" if diamond_message and varying else
                      "unknown" if diamond_message or tile_unknown else "absent")
    effects["diamond_tiling"] = _effect(diamond_status,
        ["Pluto reported Concurrent start hyperplanes found", *tiled_stages] if diamond_message else tiled_stages)
    effects["rectangular_tiling"] = _effect("absent" if diamond_status == "observed" else tiled_status, tiled_stages)
    two_level = any(row["level"] is not None and row["level"] >= 2 for row in varying)
    effects["two_level_tiling"] = _effect("observed" if two_level else "unknown" if tile_unknown else "absent", tiled_stages)
    # Phase observations above remain observations of individual proposals.
    # Their union does not identify one baseline for comparison with final C.
    selection = select_candidate(case_dir)
    result['producer_selection'] = selection
    chosen = None
    final = final_base = None
    if selection['status'] == 'selected':
        selected = selection['selected']
        chosen = next((output for output in captured_outputs
                       if str(output[0].resolve()) == selected['file']), None)
        result['producer_c_sha256'] = selected['sha256']
    elif selection['status'].startswith('unpaired-'):
        result['errors'].append(selection['status'])
    if chosen is not None:
        last_c, final, final_base, pragmas = chosen
        result["producer_c_file"] = str(last_c.resolve()) if last_c.exists() else None
        effects["parallelization"] = _effect("unknown" if pragmas else "absent", pragmas,
            reason="A pragma alone does not establish a non-singleton parallel loop; final-loop analysis must check it.")
    if final is not None and final_base is not None:
        try:
            kept = compiler_kept_rows(final)
            geometry = floor_coordinates(final_base, final)
            result["final_geometry"] = {
                "scop": final.path, "base_scop": final_base.path,
                "canonical_kept_schedule_rows": kept,
                "tile_schedule_rows": sorted({r for stmt in geometry for r in stmt["tile_schedule_rows"]}),
                "statements": geometry,
                "indexing": "zero-based raw scattering rows; keep all but globally zero coordinates, as PolyLang does; Pluto variable is t{row+1}; PolCert index is its position among kept rows",
            }
        except ScopError as error:
            result["errors"].append("final geometry: " + str(error))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case_dir", type=Path)
    args = parser.parse_args()
    print(json.dumps(analyze_producer(args.case_dir), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
