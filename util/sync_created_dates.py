#!/usr/bin/env python3
"""Copy creation dates from matching Python lemmas to Lean files.

A Python lemma in Lemma/... and a Lean lemma in ../lean/Lemma/... are paired by
lemma path: ``.given.`` is normalized to ``.of.`` (as in the axiom hierarchy),
path segment ``Is`` is normalized to ``is`` (Python reserves ``is``; Lean does
not), path segment ``In`` is normalized to ``in`` (Python reserves ``in``),
then any trailing all-lowercase segment is dropped (e.g.
``Nat.AddAdd.comm`` and ``Nat.AddAdd`` share path ``Nat.AddAdd``;
``Bool.Imp.given.ImpEq`` matches ``Bool.Imp.of.ImpEq``;
``Bool.And_Or.Is.OrAndS`` matches ``Bool.And_Or.is.OrAndS``). When the Python
``# created on YYYY-MM-DD`` date differs from the Lean file, it is written as
``-- created on YYYY-MM-DD``.

Usage:
  python util/sync_created_dates.py
  python util/sync_created_dates.py --module Nat.LtMulS.of.Lt.Lt.Ge_0.Ge_0
  python util/sync_created_dates.py --dry-run
  python util/sync_created_dates.py --list-paths
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

PY_ROOT = Path(__file__).resolve().parents[1]
ROOT = PY_ROOT.parent / "lean"
LEMMA_DIR = ROOT / "Lemma"

CREATE_RE_PY = re.compile(r"#\s*created on (\d{4}-\d{2}-\d{2})", re.I)
CREATE_RE_LEAN = re.compile(r"^--\s*created on (\d{4}-\d{2}-\d{2})\s*$", re.I)
LEMMA_PATH_RE = re.compile(r"\.[a-z]+$")

PY_KEYWORD_SEGMENTS = {
    "Is": "is",
    "In": "in",
}
LEAN_KEYWORD_SEGMENTS = {v: k for k, v in PY_KEYWORD_SEGMENTS.items()}


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")


def write_text(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8", newline="\n")


def lemma_path(module: str) -> str:
    """Drop a trailing all-lowercase segment (e.g. Nat.AddAdd.comm → Nat.AddAdd)."""
    return LEMMA_PATH_RE.sub("", module)


def py_keyword_to_lean_segment(module: str) -> str:
    """Python lemma paths capitalize reserved words; Lean uses lowercase."""
    return ".".join(PY_KEYWORD_SEGMENTS.get(part, part) for part in module.split("."))


def lean_keyword_to_py_segment(module: str) -> str:
    """Reverse mapping for Python filesystem lookup."""
    return ".".join(LEAN_KEYWORD_SEGMENTS.get(part, part) for part in module.split("."))


def normalize_lemma_path(module: str) -> str:
    """Normalize for cross-repo comparison (given→of, keyword segments, suffix)."""
    module = module.replace(".given.", ".of.")
    module = py_keyword_to_lean_segment(module)
    return lemma_path(module)


def py_module_variants(path: str) -> list[str]:
    """Filesystem paths to search under PY_ROOT/Lemma for a normalized path."""
    py_path = lean_keyword_to_py_segment(path)
    variants = [py_path]
    given = py_path.replace(".of.", ".given.")
    if given != py_path:
        variants.append(given)
    return variants


def module_name_for(lean_file: Path) -> str:
    rel = lean_file.relative_to(LEMMA_DIR).as_posix()
    if not rel.endswith(".lean"):
        raise ValueError(f"expected Lemma/*.lean, got {rel}")
    return rel[:-5].replace("/", ".")


def iter_py_theorems() -> list[Path]:
    files: list[Path] = []
    for py_file in sorted((PY_ROOT / "Lemma").rglob("*.py")):
        if is_py_theorem(py_file):
            files.append(py_file)
    return files


def lean_path_index() -> dict[str, Path]:
    index: dict[str, Path] = {}
    for lean_file in iter_lean_files():
        path = normalize_lemma_path(module_name_for(lean_file))
        index.setdefault(path, lean_file)
    return index


def list_path_matches() -> list[tuple[str, str, Path, Path]]:
    """Return (py_module, path, py_file, lean_file) for each path match."""
    index = lean_path_index()
    matches: list[tuple[str, str, Path, Path]] = []
    for py_file in iter_py_theorems():
        py_module = py_to_module(py_file)
        path = normalize_lemma_path(py_module)
        lean_file = index.get(path)
        if lean_file is not None:
            matches.append((py_module, path, py_file, lean_file))
    return matches


def print_path_matches() -> None:
    matches = list_path_matches()
    for py_module, path, py_file, lean_file in matches:
        print(
            f"{py_module}\t{path}\t"
            f"{py_file.relative_to(PY_ROOT).as_posix()}\t"
            f"{lean_file.relative_to(ROOT).as_posix()}"
        )
    print(f"total: {len(matches)}")


def module_to_py(module: str) -> Path:
    rel = module.replace(".", "/")
    py = PY_ROOT / "Lemma" / f"{rel}.py"
    if py.exists():
        return py
    return PY_ROOT / "Lemma" / rel / "__init__.py"


def py_files_for_lemma_path(path: str) -> list[Path]:
    """Python lemmas that share the same normalized path as a Lean module name."""
    found: list[Path] = []
    seen: set[Path] = set()

    def add(candidate: Path) -> None:
        if candidate.exists() and candidate not in seen:
            seen.add(candidate)
            found.append(candidate)

    for variant in py_module_variants(path):
        add(module_to_py(variant))
        rel = variant.replace(".", "/")
        subdir = PY_ROOT / "Lemma" / rel
        if subdir.is_dir():
            for candidate in sorted(subdir.glob("*.py")):
                if candidate.name != "__init__.py":
                    add(candidate)
    return found


def py_to_module(py_file: Path) -> str:
    module: list[str] = []
    current = py_file
    while current.name != "Lemma":
        module.append(current.stem if current.suffix else current.name)
        current = current.parent
    if module and module[0] == "__init__":
        module.pop(0)
    module.reverse()
    return ".".join(module)


def is_py_theorem(py_file: Path) -> bool:
    for line in read_text(py_file).splitlines():
        if not line.strip():
            continue
        if line.startswith("from util import"):
            return True
        if line.startswith("from . import"):
            return False
        break
    return False


def parse_created_date_py(py_file: Path) -> str | None:
    for line in reversed(read_text(py_file).splitlines()):
        match = CREATE_RE_PY.search(line)
        if match:
            return match.group(1)
    return None


def parse_created_date_lean(lean_file: Path) -> str | None:
    for line in reversed(read_text(lean_file).splitlines()):
        match = CREATE_RE_LEAN.match(line.strip())
        if match:
            return match.group(1)
    return None


def set_lean_created_date(content: str, created: str) -> str:
    lines = content.splitlines()
    created_line = f"-- created on {created}"
    created_index = None
    for index, line in enumerate(lines):
        if CREATE_RE_LEAN.match(line.strip()):
            created_index = index
            break

    if created_index is not None:
        if lines[created_index].strip() == created_line:
            return content
        lines[created_index] = created_line
        return "\n".join(lines).rstrip() + "\n"

    if lines and lines[-1].strip() == "":
        lines.append(created_line)
    else:
        if lines and lines[-1].strip() != "":
            lines.append("")
        lines.append(created_line)
    return "\n".join(lines).rstrip() + "\n"


def iter_lean_files(module: str | None = None) -> list[Path]:
    if module:
        module = py_keyword_to_lean_segment(module.replace(".given.", ".of."))
        rel = module.replace(".", "/") + ".lean"
        path = LEMMA_DIR / rel
        if not path.exists():
            raise FileNotFoundError(f"Lean file not found for module {module}: {path}")
        return [path]

    files: list[Path] = []
    for path in sorted(LEMMA_DIR.rglob("*.lean")):
        if ".echo." in path.name:
            continue
        files.append(path)
    return files


def pick_py_file_for_date(lean_file: Path, path: str) -> Path | None:
    """Choose a Python lemma for creation-date sync on a normalized path."""
    lean_module = module_name_for(lean_file)
    candidates: list[Path] = []
    for py_file in py_files_for_lemma_path(path):
        if normalize_lemma_path(py_to_module(py_file)) != path:
            continue
        if parse_created_date_py(py_file) is None:
            continue
        candidates.append(py_file)
    if not candidates:
        return None
    if len(candidates) == 1:
        return candidates[0]

    def module_key(module: str) -> str:
        return normalize_lemma_path(module).lower()

    lean_key = module_key(lean_module)
    exact = [py for py in candidates if module_key(py_to_module(py)) == lean_key]
    if len(exact) == 1:
        return exact[0]

    leaf = lean_module.split(".")[-1]
    leaf_match = [py for py in candidates if py.stem == leaf]
    if len(leaf_match) == 1:
        return leaf_match[0]

    return sorted(candidates, key=lambda candidate: candidate.as_posix())[0]


def apply_created_date(
    lean_file: Path,
    py_file: Path,
    path: str,
    *,
    dry_run: bool = False,
) -> str | None:
    created = parse_created_date_py(py_file)
    if created is None:
        return None

    current = parse_created_date_lean(lean_file)
    if current == created:
        return "unchanged"

    rel = lean_file.relative_to(ROOT).as_posix()
    if dry_run:
        print(
            f"would set created on {created} for {rel} "
            f"(from {py_file.relative_to(PY_ROOT)}, path {path})"
        )
        return "would-update"

    new_content = set_lean_created_date(read_text(lean_file), created)
    write_text(lean_file, new_content)
    print(f"updated {rel}: created on {created} (path {path})")
    return "updated"


def process_file(lean_file: Path, *, dry_run: bool = False) -> str | None:
    path = normalize_lemma_path(module_name_for(lean_file))
    py_file = pick_py_file_for_date(lean_file, path)
    if py_file is None:
        return None
    return apply_created_date(lean_file, py_file, path, dry_run=dry_run)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", help="process a single module name")
    parser.add_argument("--dry-run", action="store_true", help="report changes without writing")
    parser.add_argument(
        "--list-paths",
        action="store_true",
        help="print Python lemmas whose normalized path exists in the Lean project",
    )
    args = parser.parse_args()

    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")

    if not PY_ROOT.exists():
        parser.error(f"Python lemma project not found: {PY_ROOT}")
    if not LEMMA_DIR.exists():
        parser.error(f"Lean lemma directory not found: {LEMMA_DIR}")

    if args.list_paths:
        print_path_matches()
        return

    counts = {"updated": 0, "would-update": 0, "unchanged": 0, "skipped": 0}
    for lean_file in iter_lean_files(args.module):
        try:
            result = process_file(lean_file, dry_run=args.dry_run)
        except Exception as exc:
            rel = lean_file.relative_to(ROOT).as_posix()
            print(f"ERROR {rel}: {exc}", file=sys.stderr)
            counts["skipped"] += 1
            continue

        if result is None:
            counts["skipped"] += 1
        elif result in counts:
            counts[result] += 1

    print(
        "done:"
        f" updated={counts['updated']}"
        f" would-update={counts['would-update']}"
        f" unchanged={counts['unchanged']}"
        f" skipped={counts['skipped']}"
    )


if __name__ == "__main__":
    main()
