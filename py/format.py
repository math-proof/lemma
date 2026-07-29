#!/usr/bin/env python3
"""Format a Lemma .lean file: remove redundant imports and add attribute docstrings.

For files with `@[main, ...] private lemma main`, generates attribute docstrings via
`sympy/parsing/AttrDocstringGen.lean` and verifies each name with `#check`.

Redundant imports are detected by trying to remove each import (in order) and
re-typechecking the file.

Usage:
  python py/format.py Lemma/Tensor/Lt0SumMul/of/GtSum_0/Ge_0/Gt_0.lean
  python py/format.py --dry-run Lemma/...
  python py/format.py --check-only Lemma/...
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GEN = ROOT / "sympy" / "parsing" / "AttrDocstringGen.lean"
SH_DIR = ROOT / "sh"

CUSTOM_ATTR_HEADS = frozenset({
    "main", "comm", "mp", "mpr", "mp.comm", "mpr.comm", "comm.is",
    "mt", "mp.mt", "mpr.mt", "left", "right", "mpr.left", "mpr.right",
    "fin", "fin.comm", "fin.mp", "fin.mpr", "val", "subst", "cast", "cast.fin",
    "mp and", "mpr and", "mp.comm and", "mpr.comm and",
})

IMPORT_LINE_RE = re.compile(r"^import ([\w.']+)\s*$")

MAIN_ATTR_RE = re.compile(
    r"@\[main,\s*([^\]]+)\]\s*\nprivate lemma main\b",
)

ATTR_DOCSTRING_RE = re.compile(
    r"/--\s*\n\| attributes \| lemma \|.*?\n-/\s*\n+(?=@\[main,\s*)",
    flags=re.DOTALL,
)

LEMMA_NAME_RE = re.compile(
    r"^\|\s*[^|]+\|\s*([^|]+?)\s*\|\s*$",
    flags=re.MULTILINE,
)


def attr_head(token: str) -> str:
    if token in ("mp and", "mpr and", "mp.comm and", "mpr.comm and"):
        return token
    return token.split()[0]


def is_custom_attr(token: str) -> bool:
    return attr_head(token) in CUSTOM_ATTR_HEADS


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")


def write_text(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8", newline="\n")


def parse_attr_tokens(attr_blob: str) -> list[str]:
    tokens: list[str] = []
    parts = [p.strip() for p in attr_blob.split(",")]
    i = 0
    while i < len(parts):
        part = parts[i]
        if part in ("mp", "mpr", "mp.comm", "mpr.comm") and i + 1 < len(parts) and parts[i + 1] == "and":
            tokens.append(f"{part} and")
            i += 2
        else:
            tokens.append(part)
            i += 1
    return tokens


def custom_attrs(tokens: list[str]) -> list[str]:
    return [t for t in tokens if t != "main" and is_custom_attr(t)]


def find_main_attr_block(content: str) -> tuple[int, str] | None:
    match = MAIN_ATTR_RE.search(content)
    if not match:
        return None
    return match.start(0), match.group(1)


def remove_attr_docstring(content: str) -> str:
    match = ATTR_DOCSTRING_RE.search(content)
    if match:
        return content[: match.start()] + content[match.end() :]
    return content


def merge_docstring(doc: str) -> str:
    lines = doc.splitlines()
    if lines and lines[0].strip() == "/--":
        lines = lines[1:]
    if lines and lines[-1].strip() == "-/":
        lines = lines[:-1]
    return "\n".join(lines)


def insert_docstring(content: str, insert_at: int, doc: str) -> str:
    before = content[:insert_at]
    after = content[insert_at:]
    if before.rstrip("\n").endswith("-/"):
        before = before.rstrip("\n")
        before = before[:-2].rstrip("\n")
        merged = merge_docstring(doc)
        return before + "\n" + merged + "\n-/\n" + after
    before = before.rstrip("\n")
    return before + "\n\n\n" + doc + "\n" + after


def rel_path_for(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def module_name_for(path: Path) -> str:
    rel = rel_path_for(path)
    if not rel.startswith("Lemma/") or not rel.endswith(".lean"):
        raise ValueError(f"expected a Lemma/*.lean path, got {rel}")
    return rel[:-5].replace("/", ".")


def parse_import_block(content: str) -> tuple[list[tuple[str, str]], str]:
    lines = content.splitlines(keepends=True)
    imports: list[tuple[str, str]] = []
    idx = 0
    while idx < len(lines):
        match = IMPORT_LINE_RE.match(lines[idx].rstrip("\n"))
        if not match:
            break
        imports.append((match.group(1), lines[idx]))
        idx += 1
    return imports, "".join(lines[idx:])


def build_content(imports: list[tuple[str, str]], rest: str) -> str:
    return "".join(line for _, line in imports) + rest


def compiles(content: str) -> bool:
    SH_DIR.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        suffix=".lean",
        delete=False,
        dir=SH_DIR,
        newline="\n",
    ) as handle:
        handle.write(content)
        check_path = Path(handle.name)

    try:
        cmd = ["lake", "env", "lean", str(check_path.relative_to(ROOT))]
        result = subprocess.run(
            cmd,
            cwd=ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
        )
        return result.returncode == 0
    finally:
        check_path.unlink(missing_ok=True)


def remove_redundant_imports(content: str) -> tuple[str, list[str]]:
    imports, rest = parse_import_block(content)
    if not imports:
        return content, []

    kept: list[tuple[str, str]] = []
    removed: list[str] = []

    for index, (module, _line) in enumerate(imports):
        candidate = build_content(kept + imports[index + 1 :], rest)
        if compiles(candidate):
            removed.append(module)
        else:
            kept.append(imports[index])

    if not removed:
        return content, []

    return build_content(kept, rest), removed


def generate_docstring(rel: str, attrs: list[str]) -> str:
    cmd = ["lake", "env", "lean", "--run", str(GEN), rel, *attrs]
    result = subprocess.run(
        cmd,
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if result.returncode != 0:
        raise RuntimeError(
            "AttrDocstringGen failed:\n"
            f"command: {' '.join(cmd)}\n"
            f"stdout:\n{result.stdout}\n"
            f"stderr:\n{result.stderr}"
        )
    doc = result.stdout.strip()
    if not doc.startswith("/--"):
        raise RuntimeError(f"unexpected AttrDocstringGen output:\n{doc}")
    return doc


def lemma_names_from_docstring(doc: str) -> list[str]:
    names: list[str] = []
    for line in doc.splitlines():
        if "attributes" in line or ":---" in line or line.strip() in ("/--", "-/"):
            continue
        match = LEMMA_NAME_RE.match(line)
        if not match:
            continue
        name = match.group(1).strip().replace("\\_", "_")
        if name:
            names.append(name)
    return names


def build_module(lean_file: Path) -> None:
    module = module_name_for(lean_file)
    cmd = ["lake", "build", module]
    result = subprocess.run(
        cmd,
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"failed to build {module}:\n{result.stdout}\n{result.stderr}"
        )


def check_lemma_names(module: str, names: list[str]) -> list[str]:
    if not names:
        return []

    failures: list[str] = []
    for name in names:
        check_source = f"import {module}\n\n#check {name}\n"
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            suffix=".lean",
            delete=False,
            dir=SH_DIR,
            newline="\n",
        ) as handle:
            handle.write(check_source)
            check_path = Path(handle.name)

        try:
            cmd = ["lake", "env", "lean", str(check_path.relative_to(ROOT))]
            result = subprocess.run(
                cmd,
                cwd=ROOT,
                capture_output=True,
                text=True,
                encoding="utf-8",
            )
        finally:
            check_path.unlink(missing_ok=True)

        if result.returncode != 0:
            detail = (result.stdout + result.stderr).strip()
            failures.append(f"{name}: {detail}" if detail else name)

    return failures


def process_docstrings(
    content: str,
    lean_file: Path,
    *,
    dry_run: bool = False,
    check_only: bool = False,
    refresh: bool = False,
) -> tuple[str, bool]:
    rel = rel_path_for(lean_file)
    module = module_name_for(lean_file)

    found = find_main_attr_block(content)
    if not found:
        return content, False

    insert_at, attr_blob = found
    attrs = custom_attrs(parse_attr_tokens(attr_blob))
    if not attrs and "main" not in parse_attr_tokens(attr_blob):
        raise ValueError(f"no custom attributes found in @[main, {attr_blob}]")

    doc = generate_docstring(rel, attrs)
    names = lemma_names_from_docstring(doc)
    print(f"generated docstring for {rel}:")
    for line in doc.splitlines():
        if line.startswith("|") and "attributes" not in line and ":---" not in line:
            print(f"  {line.strip()}")

    print(f"building {rel} ...")
    build_module(lean_file)

    print("checking generated lemma names ...")
    failures = check_lemma_names(module, names)
    if failures:
        raise RuntimeError(
            "#check failed for:\n  " + "\n  ".join(failures)
        )
    print(f"ok: #check passed for {len(names)} name(s)")

    existing = ATTR_DOCSTRING_RE.search(content)
    if existing and existing.group(0).strip() == doc.strip() and not refresh:
        print(f"docstring unchanged: {rel}")
        return content, False

    if check_only:
        print(f"check-only: would update docstring for {rel}")
        return content, False

    new_content = content
    if existing:
        new_content = remove_attr_docstring(new_content)
        found = find_main_attr_block(new_content)
        if not found:
            raise ValueError(f"lost @[main, ...] after removing docstring in {rel}")
        insert_at, _ = found

    new_content = insert_docstring(new_content, insert_at, doc)

    if dry_run:
        print(f"dry-run: would update docstring for {rel}")
        return content, False

    return new_content, True


def process_file(
    lean_file: Path,
    *,
    dry_run: bool = False,
    check_only: bool = False,
    refresh: bool = False,
) -> None:
    content = read_text(lean_file)
    rel = rel_path_for(lean_file)
    changed = False

    print(f"checking imports for {rel} ...")
    import_content, removed = remove_redundant_imports(content)
    if removed:
        print("removed redundant imports:")
        for module in removed:
            print(f"  import {module}")
        if check_only:
            print(f"check-only: would remove {len(removed)} import(s) from {rel}")
        elif dry_run:
            print(f"dry-run: would remove {len(removed)} import(s) from {rel}")
        else:
            content = import_content
            changed = True
    else:
        print("imports ok: no redundant imports")

    content, doc_changed = process_docstrings(
        content,
        lean_file,
        dry_run=dry_run,
        check_only=check_only,
        refresh=refresh,
    )
    changed = changed or doc_changed

    if changed and not dry_run and not check_only:
        write_text(lean_file, content)
        print(f"updated {rel}")
    elif not changed:
        print(f"unchanged: {rel}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Format a Lemma .lean file (imports + attribute docstrings).",
    )
    parser.add_argument(
        "lean_file",
        help="path to a Lemma .lean file (e.g. Lemma/Tensor/Lt0SumMul/of/GtSum_0/Ge_0/Gt_0.lean)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="analyze and verify, but do not write the file",
    )
    parser.add_argument(
        "--check-only",
        action="store_true",
        help="verify changes, but do not write the file",
    )
    parser.add_argument(
        "--refresh",
        action="store_true",
        help="rewrite the docstring even if it already matches",
    )
    args = parser.parse_args()

    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")

    lean_file = Path(args.lean_file)
    if not lean_file.is_absolute():
        lean_file = ROOT / lean_file
    lean_file = lean_file.resolve()

    if not lean_file.exists():
        parser.error(f"file not found: {lean_file}")

    try:
        process_file(
            lean_file,
            dry_run=args.dry_run,
            check_only=args.check_only,
            refresh=args.refresh,
        )
    except (RuntimeError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
