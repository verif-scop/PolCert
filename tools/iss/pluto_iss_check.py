#!/usr/bin/env python3

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
import re
import sys


@dataclass(frozen=True)
class Constraint:
    rel: str
    coeffs: tuple[tuple[str, int], ...]
    const: int

    def coeff_map(self) -> dict[str, int]:
        return dict(self.coeffs)

    def key(self) -> tuple[str, tuple[tuple[str, int], ...], int]:
        return (self.rel, self.coeffs, self.const)


@dataclass
class Stmt:
    stmt_id: int
    text: str
    dim: int
    orig_depth: int
    domain: list[Constraint]
    trans: str
    reads: list[str]
    writes: list[str]
    orig_loops: list[bool]

    def payload_key(self) -> tuple:
        return (
            self.text,
            self.dim,
            self.orig_depth,
            self.trans,
            tuple(self.reads),
            tuple(self.writes),
            tuple(self.orig_loops),
        )


@dataclass
class Dep:
    dep_id: int
    src: int
    dst: int
    dep_type: str
    dpoly: list[Constraint]


@dataclass
class Program:
    nvar: int
    npar: int
    params: list[str]
    stmts: list[Stmt]
    deps: list[Dep]


def normalize_coeffs(coeffs: dict[str, int]) -> tuple[tuple[str, int], ...]:
    return tuple(sorted((k, v) for k, v in coeffs.items() if v != 0))


def parse_affine(expr: str) -> tuple[tuple[tuple[str, int], ...], int]:
    s = expr.replace(" ", "")
    if not s:
        return (), 0
    if s[0] not in "+-":
        s = "+" + s
    i = 0
    coeffs: dict[str, int] = defaultdict(int)
    const = 0
    while i < len(s):
        if s[i] not in "+-":
            raise ValueError(f"unsupported affine syntax at {s[i:]!r}")
        sign = 1 if s[i] == "+" else -1
        i += 1
        j = i
        while j < len(s) and s[j].isdigit():
            j += 1
        if j > i:
            num = int(s[i:j])
        else:
            num = 1
        if j < len(s) and (s[j].isalpha() or s[j] in "_$"):
            k = j + 1
            while k < len(s) and (s[k].isalnum() or s[k] in "_$'"):
                k += 1
            var = s[j:k]
            coeffs[var] += sign * num
            i = k
        else:
            if j == i or (j < len(s) and s[j] not in "+-"):
                raise ValueError(f"unsupported affine syntax at {s[i:]!r}")
            const += sign * num
            i = j
    return normalize_coeffs(coeffs), const


def parse_constraint(line: str) -> Constraint:
    line = line.strip()
    if line.endswith(">= 0"):
        expr = line[: -len(">= 0")].strip()
        coeffs, const = parse_affine(expr)
        return Constraint("ge", coeffs, const)
    if line.endswith("= 0"):
        expr = line[: -len("= 0")].strip()
        coeffs, const = parse_affine(expr)
        return Constraint("eq", coeffs, const)
    raise ValueError(f"unsupported constraint line: {line}")


def parse_set(lines: list[str], i: int) -> tuple[list[Constraint], int]:
    while i < len(lines) and not lines[i].startswith("Set #"):
        i += 1
    if i >= len(lines):
        raise ValueError("expected Set # block")
    i += 2  # skip Set #... and [.. constraints]
    constraints: list[Constraint] = []
    while i < len(lines) and lines[i].strip():
        constraints.append(parse_constraint(lines[i]))
        i += 1
    while i < len(lines) and not lines[i].strip():
        i += 1
    return constraints, i


_stmt_re = re.compile(r'^S(\d+) "(.*)"$')
_dims_re = re.compile(r"^ndims: (\d+); orig_depth: (\d+)$")
_trans_re = re.compile(r"^T\(S\d+\): (.*)$")
_dep_re = re.compile(
    r"^--- Dep (\d+) from S(\d+) to S(\d+); satisfied: .*; Type: ([A-Z]+)$"
)


def parse_stmt(lines: list[str], i: int) -> tuple[Stmt, int]:
    m = _stmt_re.match(lines[i])
    if not m:
        raise ValueError(f"expected stmt header at line: {lines[i]}")
    stmt_id = int(m.group(1))
    text = m.group(2)
    i += 1

    m = _dims_re.match(lines[i])
    if not m:
        raise ValueError(f"expected dims at line: {lines[i]}")
    dim = int(m.group(1))
    orig_depth = int(m.group(2))
    i += 1

    if lines[i] != "Index set":
        raise ValueError(f"expected Index set at line: {lines[i]}")
    i += 1
    domain, i = parse_set(lines, i)

    m = _trans_re.match(lines[i])
    if not m:
        raise ValueError(f"expected transformation at line: {lines[i]}")
    trans = m.group(1).strip()
    i += 1

    if i < len(lines) and lines[i].startswith("loop types"):
        i += 1
    while i < len(lines) and not lines[i].strip():
        i += 1

    reads: list[str] = []
    writes: list[str] = []
    if lines[i] == "No Read accesses":
        i += 1
    elif lines[i] == "Read accesses":
        i += 1
        while i < len(lines) and lines[i] not in ("Write accesses", "No write access") and not lines[i].startswith("Original loop:"):
            reads.append(lines[i].strip())
            i += 1
    if lines[i] == "No write access":
        i += 1
    elif lines[i] == "Write accesses":
        i += 1
        while i < len(lines) and not lines[i].startswith("Original loop:"):
            writes.append(lines[i].strip())
            i += 1

    orig_loops: list[bool] = []
    while i < len(lines) and lines[i].startswith("Original loop:"):
        orig_loops.append(lines[i].strip().endswith("yes"))
        i += 1

    while i < len(lines) and not lines[i].strip():
        i += 1

    return Stmt(stmt_id, text, dim, orig_depth, domain, trans, reads, writes, orig_loops), i


def parse_dep(lines: list[str], i: int) -> tuple[Dep, int]:
    m = _dep_re.match(lines[i])
    if not m:
        raise ValueError(f"expected dep header at line: {lines[i]}")
    dep_id = int(m.group(1))
    src = int(m.group(2))
    dst = int(m.group(3))
    dep_type = m.group(4)
    i += 1

    if i < len(lines) and lines[i].startswith("on variable:"):
        i += 1
    if lines[i] != "Dependence polyhedron":
        raise ValueError(f"expected Dependence polyhedron at line: {lines[i]}")
    i += 1
    dpoly, i = parse_set(lines, i)
    return Dep(dep_id, src, dst, dep_type, dpoly), i


def parse_program(text: str) -> Program:
    lines = text.splitlines()
    start = None
    for idx, line in enumerate(lines):
        if line == "After ISS":
            start = idx + 1
            break
    if start is None:
        for idx, line in enumerate(lines):
            if line.startswith("nvar = "):
                start = idx
                break
    if start is None:
        raise ValueError("could not locate PlutoProg dump")

    i = start
    while i < len(lines) and not lines[i].startswith("nvar = "):
        i += 1
    m = re.match(r"^nvar = (\d+), npar = (\d+)$", lines[i])
    if not m:
        raise ValueError(f"bad nvar line: {lines[i]}")
    nvar = int(m.group(1))
    npar = int(m.group(2))
    i += 1
    if not lines[i].startswith("Parameters: "):
        raise ValueError(f"bad Parameters line: {lines[i]}")
    params = [p for p in lines[i][len("Parameters: ") :].split() if p]
    i += 1

    stmts: list[Stmt] = []
    while i < len(lines) and lines[i].startswith("S"):
        stmt, i = parse_stmt(lines, i)
        stmts.append(stmt)

    deps: list[Dep] = []
    while i < len(lines) and lines[i].startswith("--- Dep"):
        dep, i = parse_dep(lines, i)
        deps.append(dep)

    return Program(nvar, npar, params, stmts, deps)


def counter_of_constraints(constraints: list[Constraint]) -> Counter[Constraint]:
    return Counter(constraints)


def counter_is_subset(sub: Counter[Constraint], sup: Counter[Constraint]) -> bool:
    for key, count in sub.items():
        if sup[key] < count:
            return False
    return True


def complement_halfspace(c: Constraint) -> Constraint:
    if c.rel != "ge":
        raise ValueError("only >= halfspaces have complements")
    coeffs = {var: -coeff for var, coeff in c.coeff_map().items()}
    return Constraint("ge", normalize_coeffs(coeffs), -c.const - 1)


def canonical_cut_key(c: Constraint) -> tuple:
    comp = complement_halfspace(c)
    a = c.key()
    b = comp.key()
    return ("cut", a if a <= b else b, b if a <= b else a)


def rename_for_dest(c: Constraint, params: set[str]) -> Constraint:
    coeffs = {}
    for var, coeff in c.coeff_map().items():
        if var in params:
            coeffs[var] = coeff
        else:
            coeffs[var + "'"] = coeff
    return Constraint(c.rel, normalize_coeffs(coeffs), c.const)


def fmt_constraint(c: Constraint) -> str:
    parts: list[str] = []
    for var, coeff in c.coeffs:
        if coeff == 1:
            parts.append(f"+{var}")
        elif coeff == -1:
            parts.append(f"-{var}")
        elif coeff > 0:
            parts.append(f"+{coeff}{var}")
        else:
            parts.append(f"{coeff}{var}")
    if c.const > 0:
        parts.append(f"+{c.const}")
    elif c.const < 0:
        parts.append(str(c.const))
    expr = "".join(parts)
    if expr.startswith("+"):
        expr = expr[1:]
    if not expr:
        expr = "0"
    rel = ">= 0" if c.rel == "ge" else "= 0"
    return f"{expr} {rel}"


def collect_var_order(
    before: Program,
    after: Program,
    global_cut_repr: dict[tuple, tuple[Constraint, Constraint]],
) -> list[str]:
    """A named serialization basis, not the source's semantic coordinates.

    Debug dumps do not declare iterator order.  PhaseISS must map every row
    by these names into the explicit source OpenScop parameter/iterator order.
    Lexicographic order here is only a reproducible wire encoding.
    """
    params = list(before.params)
    if len(params) != len(set(params)):
        raise ValueError("duplicate parameter names in ISS dump")
    nonparams: set[str] = set()

    def add_constraint_vars(c: Constraint) -> None:
        for var, _ in c.coeffs:
            if var not in params:
                nonparams.add(var)

    for prog in (before, after):
        for stmt in prog.stmts:
            for c in stmt.domain:
                add_constraint_vars(c)
    for c1, c2 in global_cut_repr.values():
        add_constraint_vars(c1)
        add_constraint_vars(c2)
    return params + sorted(nonparams)


def constraint_to_domain_rows(c: Constraint, var_order: list[str]) -> list[dict]:
    coeff_map = c.coeff_map()
    if len(var_order) != len(set(var_order)):
        raise ValueError("duplicate names in ISS bridge VAR_ORDER")
    if any(coeff and var not in var_order for var, coeff in coeff_map.items()):
        raise ValueError("ISS bridge VAR_ORDER omits a nonzero constraint variable")
    coeffs = [coeff_map.get(var, 0) for var in var_order]
    if c.rel == "ge":
        return [{"coeffs": [-x for x in coeffs], "const": c.const}]
    if c.rel == "eq":
        return [
            {"coeffs": [-x for x in coeffs], "const": c.const},
            {"coeffs": coeffs, "const": -c.const},
        ]
    raise ValueError(f"unsupported relation for bridge row: {c.rel}")


def domain_to_bridge_rows(domain: list[Constraint], var_order: list[str]) -> list[dict]:
    rows: list[dict] = []
    for c in domain:
        rows.extend(constraint_to_domain_rows(c, var_order))
    return rows


def encode_row(row: dict) -> str:
    coeffs = ",".join(str(x) for x in row["coeffs"])
    return f"{coeffs}|{row['const']}"


def encode_bridge_text(bridge: dict) -> str:
    lines: list[str] = []
    var_order = bridge["var_order"]
    lines.append(f"VAR_ORDER {len(var_order)}")
    for var in var_order:
        lines.append(f"VAR {var}")
    before_domains = bridge["before"]["stmt_domains"]
    lines.append(f"BEFORE_STMTS {len(before_domains)}")
    for domain in before_domains:
        lines.append(f"BEFORE_DOMAIN {len(domain)}")
        for row in domain:
            lines.append(f"ROW {encode_row(row)}")
    after_domains = bridge["after"]["stmt_domains"]
    lines.append(f"AFTER_STMTS {len(after_domains)}")
    for domain in after_domains:
        lines.append(f"AFTER_DOMAIN {len(domain)}")
        for row in domain:
            lines.append(f"ROW {encode_row(row)}")
    cuts = bridge["witness"]["cuts"]
    lines.append(f"CUTS {len(cuts)}")
    for cut in cuts:
        lines.append(f"CUT {encode_row(cut)}")
    stmt_ws = bridge["witness"]["stmt_witnesses"]
    lines.append(f"STMT_WITNESSES {len(stmt_ws)}")
    for stmt_w in stmt_ws:
        signs = ",".join(stmt_w["piece_signs"])
        lines.append(f"STMT_WITNESS {stmt_w['parent_stmt']} {signs}")
    lines.append("END")
    return "\n".join(lines)


def collect_iss_structure(before: Program, after: Program) -> tuple[list[str], dict]:
    messages: list[str] = []
    if before.npar != len(before.params) or after.npar != len(after.params):
        raise ValueError("ISS dump parameter name/count mismatch")
    if before.params != after.params:
        raise ValueError("ISS changed the ordered parameter list")
    before_by_payload: dict[tuple, Stmt] = {}
    for stmt in before.stmts:
        key = stmt.payload_key()
        if key in before_by_payload:
            raise ValueError("non-unique source payload; scratch checker is ambiguous")
        before_by_payload[key] = stmt

    after_families: dict[tuple, list[Stmt]] = defaultdict(list)
    for stmt in after.stmts:
        key = stmt.payload_key()
        if key not in before_by_payload:
            raise ValueError(f"after stmt S{stmt.stmt_id} has no source payload match")
        after_families[key].append(stmt)

    if set(before_by_payload) != set(after_families):
        missing = set(before_by_payload) - set(after_families)
        raise ValueError(f"missing split families for {len(missing)} source statements")

    family_cut_sets: list[set[tuple]] = []
    after_stmt_info: dict[int, tuple[int, tuple, list[Constraint]]] = {}
    payload_to_source_id = {k: stmt.stmt_id for k, stmt in before_by_payload.items()}
    source_id_to_index = {stmt.stmt_id: idx for idx, stmt in enumerate(before.stmts)}
    witness_families: list[dict] = []
    global_cut_repr: dict[tuple, tuple[Constraint, Constraint]] = {}

    for key, src in before_by_payload.items():
        pieces = sorted(after_families[key], key=lambda s: s.stmt_id)
        src_dom = counter_of_constraints(src.domain)
        piece_doms = [counter_of_constraints(piece.domain) for piece in pieces]
        common = piece_doms[0].copy()
        for dom in piece_doms[1:]:
            common &= dom
        if common != src_dom:
            raise ValueError(f"S{src.stmt_id}: common piece domain != source domain")

        extras: list[list[Constraint]] = []
        for piece, dom in zip(pieces, piece_doms):
            extra_counter = dom - common
            extra = list(extra_counter.elements())
            extras.append(extra)
            if piece.trans != src.trans:
                raise ValueError(f"S{src.stmt_id}: ISS changed transformation under --identity")
            after_stmt_info[piece.stmt_id] = (src.stmt_id, key, extra)

        extra_sizes = {len(extra) for extra in extras}
        if len(extra_sizes) != 1:
            raise ValueError(f"S{src.stmt_id}: inconsistent number of extra cut constraints")
        k = next(iter(extra_sizes))
        cut_keys = {canonical_cut_key(c) for extra in extras for c in extra}
        if len(cut_keys) != k:
            raise ValueError(f"S{src.stmt_id}: recovered cut count mismatch")
        if len(pieces) != 2 ** k:
            raise ValueError(f"S{src.stmt_id}: piece count {len(pieces)} is not 2^k")
        for extra in extras:
            if {canonical_cut_key(c) for c in extra} != cut_keys:
                raise ValueError(f"S{src.stmt_id}: each piece must pick one side of every cut")
        for cut_key in cut_keys:
            variants = Counter(
                c.key() for extra in extras for c in extra if canonical_cut_key(c) == cut_key
            )
            if len(variants) != 2:
                raise ValueError(f"S{src.stmt_id}: cut does not have exactly two halfspaces")
            c1 = next(c for extra in extras for c in extra if canonical_cut_key(c) == cut_key)
            c2 = None
            for extra in extras:
                for c in extra:
                    if canonical_cut_key(c) == cut_key and c.key() != c1.key():
                        c2 = c
                        break
                if c2 is not None:
                    break
            if c2 is None or complement_halfspace(c1).key() != c2.key():
                raise ValueError(f"S{src.stmt_id}: cut halfspaces are not complementary")
            ordered = (c1, c2) if c1.key() <= c2.key() else (c2, c1)
            global_cut_repr[cut_key] = ordered
        family_cut_sets.append(cut_keys)
        messages.append(
            f"S{src.stmt_id}: split into {len(pieces)} pieces with {k} cut(s)"
        )
        witness_families.append(
            {
                "source_stmt_id": src.stmt_id,
                "source_stmt_index": source_id_to_index[src.stmt_id],
                "piece_stmt_ids": [piece.stmt_id for piece in pieces],
                "source_domain": [fmt_constraint(c) for c in src.domain],
                "piece_signatures": {
                    str(piece.stmt_id): [
                        {
                            "cut": fmt_constraint(global_cut_repr[canonical_cut_key(c)][0]),
                            "halfspace": fmt_constraint(c),
                        }
                        for c in extra
                    ]
                    for piece, extra in zip(pieces, extras)
                },
            }
        )

    if family_cut_sets:
        first = family_cut_sets[0]
        for idx, cut_set in enumerate(family_cut_sets[1:], start=2):
            if cut_set != first:
                raise ValueError(
                    f"source family {idx} uses a different global cut set; Pluto ISS should be uniform"
                )
        messages.append(f"global_cut_count: {len(first)}")
        for cut_key in sorted(first):
            sample, other = global_cut_repr[cut_key]
            messages.append(
                "cut_pair: "
                + fmt_constraint(sample)
                + "  ||  "
                + fmt_constraint(other)
            )

    params = set(before.params)
    source_deps_by_meta: dict[tuple[int, int, str], list[Dep]] = defaultdict(list)
    for dep in before.deps:
        source_deps_by_meta[(dep.src, dep.dst, dep.dep_type)].append(dep)

    explained = 0
    for dep in after.deps:
        src_source_id, _, src_extra = after_stmt_info[dep.src]
        dst_source_id, _, dst_extra = after_stmt_info[dep.dst]
        expected_extra = counter_of_constraints(src_extra)
        expected_extra += counter_of_constraints([rename_for_dest(c, params) for c in dst_extra])
        dep_counter = counter_of_constraints(dep.dpoly)
        if not counter_is_subset(expected_extra, dep_counter):
            raise ValueError(f"after dep {dep.dep_id} is missing expected cut constraints")
        base_counter = dep_counter - expected_extra
        matched = False
        for src_dep in source_deps_by_meta[(src_source_id, dst_source_id, dep.dep_type)]:
            if counter_of_constraints(src_dep.dpoly) == base_counter:
                matched = True
                break
        if not matched:
            raise ValueError(
                f"after dep {dep.dep_id} could not be explained by a source dep plus cut remapping"
            )
        explained += 1

    messages.append(f"after_deps_explained: {explained}/{len(after.deps)}")
    witness = {
        "params": before.params,
        "cuts": [
            {
                "nonnegative_halfspace": fmt_constraint(global_cut_repr[cut_key][0]),
                "negative_halfspace": fmt_constraint(global_cut_repr[cut_key][1]),
                "hyperplane": fmt_constraint(
                    Constraint(
                        "eq",
                        global_cut_repr[cut_key][0].coeffs,
                        global_cut_repr[cut_key][0].const,
                    )
                ),
            }
            for cut_key in sorted(global_cut_repr)
        ],
        "families": witness_families,
        "after_dep_count": len(after.deps),
    }
    var_order = collect_var_order(before, after, global_cut_repr)
    sorted_cut_keys = sorted(global_cut_repr)
    bridge = {
        "var_order": var_order,
        "before": {
            "stmt_domains": [
                domain_to_bridge_rows(stmt.domain, var_order) for stmt in before.stmts
            ],
        },
        "after": {
            "stmt_domains": [
                domain_to_bridge_rows(stmt.domain, var_order) for stmt in after.stmts
            ],
        },
        "witness": {
            "cuts": [
                {
                    "coeffs": [
                        dict(global_cut_repr[cut_key][0].coeffs).get(var, 0)
                        for var in var_order
                    ],
                    "const": global_cut_repr[cut_key][0].const,
                }
                for cut_key in sorted_cut_keys
            ],
            "stmt_witnesses": [
                {
                    "parent_stmt": source_id_to_index[src_id],
                    "piece_signs": [
                        (
                            "ge"
                            if any(
                                canonical_cut_key(c) == cut_key
                                and c.key() == global_cut_repr[cut_key][0].key()
                                for c in extra
                            )
                            else "lt"
                        )
                        for cut_key in sorted_cut_keys
                    ],
                }
                for stmt in after.stmts
                for (src_id, _, extra) in [after_stmt_info[stmt.stmt_id]]
            ],
        },
    }
    return messages, {"witness": witness, "bridge": bridge}


def validate(before: Program, after: Program) -> list[str]:
    messages, _ = collect_iss_structure(before, after)
    return messages


def split_combined_debug_dump(text: str) -> tuple[str, str]:
    lines = text.splitlines()
    for idx, line in enumerate(lines):
        if line.strip() == "After ISS":
            before = "\n".join(lines[:idx]).strip()
            after = "\n".join(lines[idx:]).strip()
            if not before:
                raise ValueError("combined Pluto dump is missing the pre-ISS section")
            if not after:
                raise ValueError("combined Pluto dump is missing the After ISS section")
            return before + "\n", after + "\n"
    raise ValueError("combined Pluto dump does not contain an After ISS marker")


def main(argv: list[str]) -> int:
    emit_json = False
    emit_bridge = False
    emit_bridge_from_combined = False
    args = argv[1:]
    if args and args[0] == "--emit-json":
        emit_json = True
        args = args[1:]
    if args and args[0] == "--emit-bridge":
        emit_bridge = True
        args = args[1:]
    if args and args[0] == "--emit-bridge-from-combined":
        emit_bridge_from_combined = True
        args = args[1:]
    if emit_bridge_from_combined:
        if len(args) != 1:
            print(
                f"usage: {argv[0]} [--emit-json|--emit-bridge] BEFORE.txt AFTER.txt",
                file=sys.stderr,
            )
            print(
                f"   or: {argv[0]} --emit-bridge-from-combined COMBINED.txt",
                file=sys.stderr,
            )
            return 2
        try:
            before_text, after_text = split_combined_debug_dump(Path(args[0]).read_text())
            before = parse_program(before_text)
            after = parse_program(after_text)
            _, payload = collect_iss_structure(before, after)
        except Exception as ex:
            print(f"validation: FAIL: {ex}")
            return 1
        print(encode_bridge_text(payload["bridge"]))
        return 0
    if len(args) != 2:
        print(
            f"usage: {argv[0]} [--emit-json|--emit-bridge] BEFORE.txt AFTER.txt",
            file=sys.stderr,
        )
        print(
            f"   or: {argv[0]} --emit-bridge-from-combined COMBINED.txt",
            file=sys.stderr,
        )
        return 2
    before = parse_program(Path(args[0]).read_text())
    after = parse_program(Path(args[1]).read_text())
    try:
        messages, payload = collect_iss_structure(before, after)
    except Exception as ex:
        print(f"validation: FAIL: {ex}")
        return 1
    if emit_bridge:
        print(encode_bridge_text(payload["bridge"]))
        return 0
    print("validation: OK")
    for msg in messages:
        print(msg)
    if emit_json:
        import json
        print(json.dumps(payload["witness"], indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
