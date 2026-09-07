#!/usr/bin/env python3
"""Test-only Pluto wrapper that corrupts a selected scheduling phase."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys


TILE_LINK_MODE = "tiling"
FINAL_AFFINE_MODE = "final-affine"
TILED_SCHEDULE_MODE = "tiling-schedule"


def generated_output(args: list[str], suffix: str) -> Path | None:
    inputs = [Path(arg).resolve() for arg in args if arg.endswith(".scop")]
    if not inputs:
        return None
    source = inputs[-1]
    candidates = (
        source.with_name(source.name + suffix),
        Path.cwd() / (source.name + suffix),
    )
    return next((path for path in candidates if path.is_file()), None)


def tiling_output(args: list[str]) -> Path | None:
    return (generated_output(args, ".posttile.scop")
            or generated_output(args, ".afterscheduling.scop"))


def identical_final_alias(args: list[str], output: Path) -> Path | None:
    """Preserve plain tiling's posttile=final contract during corruption."""
    if "--diamond-tile" in args or "--full-diamond-tile" in args:
        return None
    final = generated_output(args, ".afterscheduling.scop")
    if final is None or final == output:
        return None
    if final.read_bytes() != output.read_bytes():
        raise ValueError("plain tiling posttile and final outputs already differ")
    return final


def corrupt_tile_link(output: Path, target_coefficients: tuple[int, ...]) -> int:
    lines = output.read_text(encoding="utf-8").splitlines(keepends=True)
    index = 0
    while index < len(lines):
        if lines[index].strip() != "DOMAIN":
            index += 1
            continue

        header = index + 1
        while header < len(lines):
            stripped = lines[header].strip()
            if stripped and not stripped.startswith("#"):
                break
            header += 1
        if header >= len(lines):
            break

        shape = lines[header].split()
        if len(shape) < 6:
            index = header + 1
            continue
        row_count, column_count, out_dim = map(int, shape[:3])
        row = header + 1
        rows_seen = 0
        while row < len(lines) and rows_seen < row_count:
            stripped = lines[row].strip()
            if not stripped or stripped.startswith("#"):
                row += 1
                continue
            newline = "\n" if lines[row].endswith("\n") else ""
            raw_line = lines[row][:-1] if newline else lines[row]
            data, marker, comment = raw_line.partition("##")
            tokens = data.split()
            if len(tokens) != column_count:
                raise ValueError(
                    f"unexpected domain row width in {output}: "
                    f"{len(tokens)} != {column_count}"
                )
            for token_index in range(1, 1 + out_dim):
                value = int(tokens[token_index])
                if value not in target_coefficients:
                    continue
                tokens[token_index] = str(value + 1)
                suffix = f"##{comment}" if marker else ""
                lines[row] = (
                    " ".join(tokens) + (f" {suffix}" if suffix else "") + newline
                )
                output.write_text("".join(lines), encoding="utf-8")
                return 1
            rows_seen += 1
            row += 1
        index = row
    return 0


def reverse_scattering_inputs(output: Path) -> int:
    lines = output.read_text(encoding="utf-8").splitlines(keepends=True)
    changed_coefficients = 0
    index = 0
    while index < len(lines):
        if lines[index].strip() != "SCATTERING":
            index += 1
            continue

        header = index + 1
        while header < len(lines):
            stripped = lines[header].strip()
            if stripped and not stripped.startswith("#"):
                break
            header += 1
        if header >= len(lines):
            break

        shape = lines[header].split()
        if len(shape) < 6:
            index = header + 1
            continue
        row_count, column_count, out_dim, in_dim = map(int, shape[:4])
        row = header + 1
        rows_seen = 0
        while row < len(lines) and rows_seen < row_count:
            stripped = lines[row].strip()
            if not stripped or stripped.startswith("#"):
                row += 1
                continue
            newline = "\n" if lines[row].endswith("\n") else ""
            raw_line = lines[row][:-1] if newline else lines[row]
            data, marker, comment = raw_line.partition("##")
            tokens = data.split()
            if len(tokens) != column_count:
                raise ValueError(
                    f"unexpected scattering row width in {output}: "
                    f"{len(tokens)} != {column_count}"
                )
            first_input = 1 + out_dim
            after_input = first_input + in_dim
            for token_index in range(first_input, after_input):
                value = int(tokens[token_index])
                if value != 0:
                    tokens[token_index] = str(-value)
                    changed_coefficients += 1
            suffix = f"##{comment}" if marker else ""
            lines[row] = " ".join(tokens) + (f" {suffix}" if suffix else "") + newline
            rows_seen += 1
            row += 1
        index = row

    if changed_coefficients:
        output.write_text("".join(lines), encoding="utf-8")
    return changed_coefficients


def main() -> int:
    real_pluto = os.environ.get("POLCERT_REAL_PLUTO", "/pluto/tool/pluto")
    mode = os.environ.get("POLCERT_REJECTING_PLUTO_MODE", TILE_LINK_MODE)
    args = sys.argv[1:]
    proc = subprocess.run([real_pluto, *args], check=False)
    if proc.returncode != 0:
        return proc.returncode
    if "--tile" not in args:
        return 0

    if mode in (TILE_LINK_MODE, TILED_SCHEDULE_MODE):
        output = tiling_output(args)
    elif mode == FINAL_AFFINE_MODE:
        if "--diamond-tile" not in args and "--full-diamond-tile" not in args:
            print(
                "[rejecting-pluto] final-affine mode requires a diamond route",
                file=sys.stderr,
            )
            return 72
        output = generated_output(args, ".afterscheduling.scop")
    else:
        print(f"[rejecting-pluto] unknown mode: {mode}", file=sys.stderr)
        return 73

    if output is None:
        print("[rejecting-pluto] missing scheduled OpenScop output", file=sys.stderr)
        return 70

    alias = (identical_final_alias(args, output)
             if mode in (TILE_LINK_MODE, TILED_SCHEDULE_MODE) else None)

    if mode == TILE_LINK_MODE:
        target_coefficients = (
            (-8, -256) if "--second-level-tile" in args else (-32,)
        )
        count = corrupt_tile_link(output, target_coefficients)
        if count != 1:
            print("[rejecting-pluto] no tiling tile-link row found", file=sys.stderr)
            return 71
        if alias is not None:
            alias.write_bytes(output.read_bytes())
        print(
            f"[rejecting-pluto] corrupted one tiling tile-link in {output.name}",
            file=sys.stderr,
        )
        return 0

    count = reverse_scattering_inputs(output)
    if count == 0:
        print("[rejecting-pluto] no final scattering input found", file=sys.stderr)
        return 71
    if alias is not None:
        alias.write_bytes(output.read_bytes())
    phase = "tiled" if mode == TILED_SCHEDULE_MODE else "final"
    print(
        f"[rejecting-pluto] reversed {count} {phase} scattering input coefficients "
        f"in {output.name}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
