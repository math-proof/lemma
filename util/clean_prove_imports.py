#!/usr/bin/env python3
"""Remove unused and duplicate ``from Lemma import ...`` lines inside ``prove``.

Usage:
  python util/clean_prove_imports.py
  python util/clean_prove_imports.py --dry-run
  python util/clean_prove_imports.py Lemma/Set/Cup/eq/Cup_UFnNeg.py
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

PY_ROOT = Path(__file__).resolve().parents[1]
LEMMA_DIR = PY_ROOT / "Lemma"

IMPORT_RE = re.compile(r"^(\s*)from Lemma import (.+?)\s*$")
PROVE_DEF_RE = re.compile(r"^def prove\(")


def get_sections() -> list[str]:
    return sorted(
        (p.name for p in LEMMA_DIR.iterdir() if p.is_dir() and p.name != "__pycache__"),
        key=len,
        reverse=True,
    )


def section_usage_re(sections: list[str]) -> re.Pattern[str]:
    return re.compile(fr"\b(?:{'|'.join(map(re.escape, sections))})(?:\.\w+)+")


def parse_import_names(import_clause: str) -> list[str]:
    return [name.strip() for name in import_clause.split(",") if name.strip()]


def dedupe_preserve_order(names: list[str]) -> list[str]:
    seen: set[str] = set()
    result: list[str] = []
    for name in names:
        if name not in seen:
            seen.add(name)
            result.append(name)
    return result


def find_prove_body_range(lines: list[str]) -> tuple[int, int] | None:
    start = next((i for i, line in enumerate(lines) if PROVE_DEF_RE.match(line)), None)
    if start is None:
        return None

    end = start + 1
    while end < len(lines):
        line = lines[end]
        stripped = line.strip()
        if not stripped:
            end += 1
            continue
        if not line[0].isspace():
            if stripped.startswith("#"):
                end += 1
                continue
            if stripped.startswith("@") or stripped.startswith("def ") or stripped.startswith("if __name__"):
                break
        end += 1
    return start, end


def used_sections_in_prove(lines: list[str], start: int, end: int, usage_re: re.Pattern[str]) -> set[str]:
    used: set[str] = set()
    for line in lines[start + 1 : end]:
        if line.lstrip().startswith("#"):
            continue
        if IMPORT_RE.match(line):
            continue
        for match in usage_re.finditer(line):
            used.add(match.group(0).split(".", 1)[0])
    return used


def clean_import_line(line: str, used: set[str]) -> str | None:
    match = IMPORT_RE.match(line)
    if not match:
        return line

    indent, import_clause = match.groups()
    names = dedupe_preserve_order(parse_import_names(import_clause))
    kept = [name for name in names if name in used]
    if not kept:
        return None
    return f"{indent}from Lemma import {', '.join(kept)}\n"


def clean_file(path: Path, sections: list[str], dry_run: bool) -> list[str]:
    text = path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")
    lines = text.splitlines(keepends=True)
    body = find_prove_body_range(lines)
    if body is None:
        return []

    start, end = body
    usage_re = section_usage_re(sections)
    used = used_sections_in_prove(lines, start, end, usage_re)

    changes: list[str] = []
    new_lines = list(lines)
    offset = 0

    for index in range(start + 1, end):
        line = lines[index]
        if not IMPORT_RE.match(line):
            continue

        old = line.rstrip("\n")
        cleaned = clean_import_line(line, used)
        if cleaned is None:
            new_lines.pop(index - offset)
            offset += 1
            changes.append(f"  - {old}")
        else:
            cleaned_line = cleaned if cleaned.endswith("\n") else cleaned + "\n"
            if cleaned_line != line:
                new_lines[index - offset] = cleaned_line
                changes.append(f"  {old} -> {cleaned_line.rstrip()}")

    if changes and not dry_run:
        path.write_text("".join(new_lines), encoding="utf-8", newline="\n")

    return changes


def iter_py_files(paths: list[Path]) -> list[Path]:
    if paths:
        files: list[Path] = []
        for path in paths:
            path = path if path.is_absolute() else PY_ROOT / path
            if path.is_dir():
                files.extend(sorted(path.rglob("*.py")))
            else:
                files.append(path)
        return files
    return sorted(LEMMA_DIR.rglob("*.py"))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", help="files or directories (default: all Lemma/*.py)")
    parser.add_argument("--dry-run", action="store_true", help="print changes without writing files")
    args = parser.parse_args(argv)

    sections = get_sections()
    changed_files = 0

    for path in iter_py_files([Path(p) for p in args.paths]):
        changes = clean_file(path, sections, args.dry_run)
        if not changes:
            continue
        changed_files += 1
        rel = path.relative_to(PY_ROOT)
        print(rel)
        for change in changes:
            print(change)

    if args.dry_run:
        print(f"\n{changed_files} file(s) would be updated.")
    else:
        print(f"\n{changed_files} file(s) updated.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
