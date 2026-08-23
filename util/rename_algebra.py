#!/usr/bin/env python3
"""Rename Algebra.* lemmas to another section and update references.

Usage:
  python util/rename_algebra.py --dry-run Algebra.Arg.simp Complex.Arg.simp
  python util/rename_algebra.py Algebra.Arg.simp Complex.Arg.simp
  python util/rename_algebra.py --map-file mappings.txt
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

PY_ROOT = Path(__file__).resolve().parents[1]
LEMMA_DIR = PY_ROOT / "Lemma"

IMPORT_LINE_RE = re.compile(r"^from \. import (.+)$")
LEMMA_IMPORT_RE = re.compile(r"^(\s*)from Lemma import (.+?)\s*$")
PROVE_DEF_RE = re.compile(r"^def prove\(")


def module_to_dir(module: str) -> Path:
    return LEMMA_DIR.joinpath(*module.split("."))


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")


def write_text(path: Path, text: str) -> None:
    if text and not text.endswith("\n"):
        text += "\n"
    last_error: OSError | None = None
    for attempt in range(8):
        try:
            path.write_text(text, encoding="utf-8", newline="\n")
            return
        except OSError as error:
            last_error = error
            time.sleep(0.25 * (attempt + 1))
    raise last_error


def is_theorem_text(text: str) -> bool:
    return bool(re.search(r"^@apply\b", text, re.M))


def find_src(module: str) -> Path:
    path = module_to_dir(module)
    py = path.with_suffix(".py")
    if py.is_file():
        return py
    init = path / "__init__.py"
    if init.is_file() and is_theorem_text(read_text(init)):
        return init
    raise FileNotFoundError(f"theorem not found: {module}")


def split_init(text: str) -> tuple[str, str]:
    theorem_lines: list[str] = []
    import_lines: list[str] = []
    for line in text.splitlines(True):
        if IMPORT_LINE_RE.match(line.rstrip("\n")):
            import_lines.append(line)
        else:
            theorem_lines.append(line)
    return "".join(theorem_lines), "".join(import_lines)


def imported_names(text: str) -> list[str]:
    names: list[str] = []
    for line in text.splitlines():
        match = IMPORT_LINE_RE.match(line)
        if not match:
            continue
        names.extend(part.strip() for part in match.group(1).split(",") if part.strip())
    return names


def insert_into_init(package_dir: Path, name: str, dry_run: bool) -> None:
    init = package_dir / "__init__.py"
    if not init.exists():
        if not dry_run:
            package_dir.mkdir(parents=True, exist_ok=True)
            write_text(init, f"from . import {name}\n")
        print(f"  create {init.relative_to(PY_ROOT)} += {name}")
        return

    text = read_text(init)
    if name in imported_names(text):
        return
    print(f"  edit  {init.relative_to(PY_ROOT)} += {name}")
    if not dry_run:
        if text and not text.endswith("\n"):
            text += "\n"
        write_text(init, text + f"from . import {name}\n")


def delete_from_init(package_dir: Path, name: str, dry_run: bool) -> None:
    init = package_dir / "__init__.py"
    if not init.exists():
        return
    text = read_text(init)
    lines = text.splitlines(True)
    changed = False
    new_lines: list[str] = []
    for line in lines:
        match = IMPORT_LINE_RE.match(line.rstrip("\n"))
        if not match:
            new_lines.append(line)
            continue
        names = [part.strip() for part in match.group(1).split(",") if part.strip()]
        if name not in names:
            new_lines.append(line)
            continue
        changed = True
        names = [part for part in names if part != name]
        if names:
            new_lines.append(f"from . import {', '.join(names)}\n")
    if not changed:
        return
    print(f"  edit  {init.relative_to(PY_ROOT)} -= {name}")
    if not dry_run:
        write_text(init, "".join(new_lines))


def convert_file_to_package(py_file: Path, dry_run: bool) -> Path:
    pkg = py_file.with_suffix("")
    dest = pkg / "__init__.py"
    print(f"  file->pkg {py_file.relative_to(PY_ROOT)} -> {dest.relative_to(PY_ROOT)}")
    if not dry_run:
        pkg.mkdir(parents=True, exist_ok=True)
        if dest.exists():
            raise RuntimeError(f"cannot convert, dest exists: {dest}")
        shutil.move(str(py_file), str(dest))
    return dest


def prepare_dest_parents(new_mod: str, dry_run: bool) -> None:
    parts = new_mod.split(".")
    current = LEMMA_DIR
    for index, part in enumerate(parts[:-1]):
        parent = current
        current = current / part
        py = current.with_suffix(".py")
        if py.is_file() and not current.is_dir():
            convert_file_to_package(py, dry_run)
        if not dry_run:
            current.mkdir(parents=True, exist_ok=True)
            init = current / "__init__.py"
            if not init.exists():
                write_text(init, "")
        insert_into_init(parent, part, dry_run)


def dest_targets(new_mod: str) -> tuple[Path, Path]:
    dest_path = module_to_dir(new_mod)
    return dest_path.with_suffix(".py"), dest_path / "__init__.py"


def merge_theorem_into_init(init: Path, theorem: str, dry_run: bool) -> None:
    if init.exists():
        existing = read_text(init)
        if is_theorem_text(existing):
            raise RuntimeError(f"destination already has a theorem: {init}")
        text = theorem.rstrip() + "\n\n" + existing.lstrip("\n")
    else:
        text = theorem
    print(f"  write {init.relative_to(PY_ROOT)} (theorem into package)")
    if not dry_run:
        init.parent.mkdir(parents=True, exist_ok=True)
        write_text(init, text)


def package_children(package_dir: Path) -> list[Path]:
    if not package_dir.is_dir():
        return []
    return [
        path
        for path in package_dir.iterdir()
        if path.name not in {"__init__.py", "__pycache__"}
        and (path.is_dir() or path.suffix == ".py")
    ]


def cleanup_empty_packages(start: Path, dry_run: bool) -> None:
    current = start
    while current != LEMMA_DIR and current.is_dir():
        init = current / "__init__.py"
        children = package_children(current)
        text = read_text(init) if init.exists() else ""
        has_apply = is_theorem_text(text)
        has_imports = bool(imported_names(text))
        leftover = "".join(
            line
            for line in text.splitlines(True)
            if line.strip() and not IMPORT_LINE_RE.match(line.rstrip("\n"))
        ).strip()
        if children or has_apply or has_imports or leftover:
            break
        name = current.name
        parent = current.parent
        print(f"  rmtree {current.relative_to(PY_ROOT)}")
        if not dry_run:
            shutil.rmtree(current)
        delete_from_init(parent, name, dry_run)
        current = parent


def path_to_module(path: Path) -> str:
    rel = path.relative_to(LEMMA_DIR)
    parts = list(rel.parts)
    if parts[-1] == "__init__.py":
        parts = parts[:-1]
    else:
        parts[-1] = Path(parts[-1]).stem
    return ".".join(parts)


def replace_references(old_mod: str, new_mod: str, dry_run: bool) -> list[Path]:
    old_lemma = f"Lemma.{old_mod}"
    new_lemma = f"Lemma.{new_mod}"
    # Match a module used as `Mod.apply` or as a bare name, but not a
    # longer child path such as `Mod.Gt_0`.
    tail = r"(?:(?=\.apply\b)|(?![\w.]))"
    pattern_lemma = re.compile(rf"(?<![\w.]){re.escape(old_lemma)}{tail}")
    pattern_mod = re.compile(rf"(?<![\w.]){re.escape(old_mod)}{tail}")
    changed: list[Path] = []

    for path in LEMMA_DIR.rglob("*.py"):
        if path.name == "__pycache__":
            continue
        text = read_text(path)
        new_text = pattern_lemma.sub(new_lemma, text)
        new_text = pattern_mod.sub(new_mod, new_text)
        if new_text == text:
            continue
        print(f"  refs  {path.relative_to(PY_ROOT)}")
        changed.append(path)
        if not dry_run:
            write_text(path, new_text)
            ensure_section_import(path, new_mod.split(".", 1)[0])
    return changed


def ensure_section_import(path: Path, section: str) -> None:
    text = read_text(path)
    lines = text.splitlines(True)
    prove_at = next((i for i, line in enumerate(lines) if PROVE_DEF_RE.match(line)), None)
    if prove_at is None:
        return

    used = re.search(rf"(?<![\w.]){re.escape(section)}\.\w+", text)
    if not used:
        return

    for index in range(prove_at + 1, min(prove_at + 20, len(lines))):
        match = LEMMA_IMPORT_RE.match(lines[index])
        if not match:
            continue
        indent, clause = match.groups()
        names = [part.strip() for part in clause.split(",") if part.strip()]
        if section in names:
            return
        names.append(section)
        lines[index] = f"{indent}from Lemma import {', '.join(names)}\n"
        if section == "Bool":
            # `from Lemma import Bool` shadows sympy.Bool in prove().
            for j in range(index + 1, len(lines)):
                if PROVE_DEF_RE.match(lines[j]) or (
                    j > prove_at and re.match(r"^(def |class |if __name__)", lines[j])
                ):
                    break
                lines[j] = re.sub(r"(?<![\w.])Bool(?![\w.])", "functions.Bool", lines[j])
        write_text(path, "".join(lines))
        return


def move_theorem(old_mod: str, new_mod: str, dry_run: bool) -> list[Path]:
    if old_mod == new_mod:
        return []
    src = find_src(old_mod)
    print(f"{old_mod} -> {new_mod}")
    print(f"  src   {src.relative_to(PY_ROOT)}")
    prepare_dest_parents(new_mod, dry_run)

    dest_py, dest_init = dest_targets(new_mod)
    dest_dir = module_to_dir(new_mod)
    last = new_mod.split(".")[-1]
    dest_parent = dest_dir.parent

    if src.name == "__init__.py":
        theorem, imports = split_init(read_text(src))
        if dest_dir.is_dir() or dest_init.exists():
            merge_theorem_into_init(dest_init, theorem, dry_run)
        elif dest_py.exists():
            raise RuntimeError(f"destination already exists: {dest_py}")
        else:
            print(f"  write {dest_py.relative_to(PY_ROOT)}")
            if not dry_run:
                dest_py.parent.mkdir(parents=True, exist_ok=True)
                write_text(dest_py, theorem)
        if dry_run:
            pass
        elif imports.strip():
            write_text(src, imports)
        else:
            write_text(src, "")
    else:
        if dest_dir.is_dir():
            merge_theorem_into_init(dest_init, read_text(src), dry_run)
            print(f"  unlink {src.relative_to(PY_ROOT)}")
            if not dry_run:
                src.unlink()
        elif dest_py.exists():
            raise RuntimeError(f"destination already exists: {dest_py}")
        else:
            print(f"  move  {src.relative_to(PY_ROOT)} -> {dest_py.relative_to(PY_ROOT)}")
            if not dry_run:
                dest_py.parent.mkdir(parents=True, exist_ok=True)
                shutil.move(str(src), str(dest_py))

    insert_into_init(dest_parent, last, dry_run)
    if src.name == "__init__.py":
        cleanup_empty_packages(src.parent, dry_run)
    else:
        delete_from_init(src.parent, old_mod.split(".")[-1], dry_run)
        cleanup_empty_packages(src.parent, dry_run)

    return replace_references(old_mod, new_mod, dry_run)


def parse_map_file(path: Path) -> list[tuple[str, str]]:
    pairs: list[tuple[str, str]] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        old, new = line.split()
        pairs.append((old, new))
    return pairs


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("old", nargs="?", help="old module, e.g. Algebra.Arg.simp")
    parser.add_argument("new", nargs="?", help="new module, e.g. Complex.Arg.simp")
    parser.add_argument("--map-file", type=Path, help="lines of: old_module new_module")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--prove", action="store_true", help="prove the new module and affected callers")
    args = parser.parse_args(argv)

    pairs: list[tuple[str, str]] = []
    if args.map_file:
        pairs.extend(parse_map_file(args.map_file))
    if args.old and args.new:
        pairs.append((args.old, args.new))
    if not pairs:
        parser.error("provide old/new or --map-file")

    pairs.sort(key=lambda pair: pair[0].count("."), reverse=True)
    affected: list[str] = []
    for old, new in pairs:
        changed = move_theorem(old, new, args.dry_run)
        affected.append(new)
        for path in changed:
            try:
                affected.append(path_to_module(path))
            except ValueError:
                continue

    if args.prove and not args.dry_run:
        modules = list(dict.fromkeys(affected))
        env = os.environ.copy()
        env["PYTHONIOENCODING"] = "utf-8"
        cmd = [sys.executable, str(PY_ROOT / "run.py"), *modules]
        print("prove", " ".join(modules))
        return subprocess.call(cmd, cwd=PY_ROOT, env=env)
    return 0


if __name__ == "__main__":
    sys.exit(main())
