#!/usr/bin/env python3
"""Delete unnecessary Lemma imports from a .lean file.

Stores indirect dependency relationships inside the existing ``meta`` JSON
column of the ``lemma`` table as ``meta.callee`` — a sorted JSON array of
modules reachable from, but not directly imported by, the module.

A pairwise compare function checks each pair of Lemma imports — n*(n-1)/2
comparisons — to find redundant imports.

Usage:
  python py/delete_import.py Lemma/Real/SomeLemma.lean
  python py/delete_import.py --dry-run Lemma/Real/SomeLemma.lean

  python py/delete_import.py --update Lemma.Real.SomeLemma
  python py/delete_import.py --rebuild
"""

from __future__ import annotations

import os
import std
os.environ['MYSQL_DATABASE'] = 'axiom'
from std import MySQL

import argparse
import json
import re
import sys
from collections.abc import Iterable
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

IMPORT_LINE_RE = re.compile(r"^import ([\w.']+)\s*$")

LEMMA_PREFIX = "Lemma."


def normalize_module(name: str) -> str:
    """DB ``module`` values are unprefixed; import lines use ``Lemma.``-prefixed names."""
    return name[len(LEMMA_PREFIX):] if name.startswith(LEMMA_PREFIX) else name


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")


def write_text(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8", newline="\n")


def rel_path_for(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def parse_import_block(content: str) -> tuple[list[tuple[str, str]], str]:
    """Split leading ``import`` lines from the rest of the file."""
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


def load_dependency_graph() -> dict[str, set[str]]:
    """Load all ``module → direct imports`` edges from the ``lemma`` table."""
    sql = (
        "SELECT DISTINCT module, jt.import "
        "FROM lemma "
        "CROSS JOIN JSON_TABLE(imports, '$[*]' "
        "COLUMNS (import VARCHAR(256) PATH '$')) AS jt"
    )
    rows = MySQL.instance.query(sql)
    graph: dict[str, set[str]] = {}
    for module, imp in rows:
        graph.setdefault(module, set()).add(normalize_module(imp))
    return graph


def compute_reach(
    graph: dict[str, set[str]],
    starts: Iterable[str] | None = None,
) -> dict[str, set[str]]:
    """Transitive imports per module, computed bottom-up over the import DAG.

    Only nodes reachable from ``starts`` (default: every module) are computed;
    pass the affected cone to avoid paying for the whole graph on ``--update``.
    Each node's set is built once from its children's already-computed sets.
    """
    reach: dict[str, set[str]] = {}
    visiting: set[str] = set()
    for start in starts if starts is not None else graph:
        if start in reach:
            continue
        stack = [(start, False)]
        while stack:
            node, expanded = stack.pop()
            if expanded:
                visiting.discard(node)
                deps: set[str] = set()
                for imp in graph.get(node, ()):
                    deps.add(imp)
                    deps |= reach.get(imp, set())
                reach[node] = deps
            elif node not in reach and node not in visiting:
                visiting.add(node)
                stack.append((node, True))
                for imp in graph.get(node, ()):
                    if imp not in reach:
                        stack.append((imp, False))
    return reach


def indirect_deps(
    module: str,
    graph: dict[str, set[str]],
    reach: dict[str, set[str]],
) -> list[str]:
    """Sorted indirect deps of ``module``: reachable minus direct imports."""
    return sorted(reach.get(module, set()) - graph.get(module, set()))


def sql_str(s: str) -> str:
    return "'" + s.replace("'", "''") + "'"


def batch_update_meta(updates: dict[str, list[str]]) -> None:
    """Set ``meta.callee`` via ``JSON_SET``, preserving other keys (e.g. ``error``)."""
    batch_size = 1000
    items = list(updates.items())
    for i in range(0, len(items), batch_size):
        batch = items[i : i + batch_size]
        case_clauses = " ".join(
            f"WHEN {sql_str(module)} THEN CAST({sql_str(json.dumps(deps))} AS JSON)"
            for module, deps in batch
        )
        modules = ", ".join(sql_str(m) for m, _ in batch)
        MySQL.instance.execute(
            f"UPDATE lemma SET meta = JSON_SET(IFNULL(meta, '{{}}'), '$.callee', "
            f"CASE module {case_clauses} END) "
            f"WHERE module IN ({modules})"
        )


def find_callers(module: str, graph: dict[str, set[str]]) -> set[str]:
    """Find all modules that transitively depend on ``module`` via reverse BFS."""
    reverse: dict[str, set[str]] = {}
    for mod, imports in graph.items():
        for imp in imports:
            reverse.setdefault(imp, set()).add(mod)

    result: set[str] = set()
    queue = [module]
    while queue:
        current = queue.pop(0)
        for caller in reverse.get(current, set()):
            if caller not in result:
                result.add(caller)
                queue.append(caller)
    return result


def update_lemma_dep(module: str) -> None:
    """Incrementally update ``meta.callee`` after ``module``'s imports changed."""
    module = normalize_module(module)
    graph = load_dependency_graph()

    callers = find_callers(module, graph)
    affected = callers | {module}
    print(f"updating {len(affected)} module(s): {module} and its callers")

    reach = compute_reach(graph, affected)
    updates = {m: indirect_deps(m, graph, reach) for m in affected}

    batch_update_meta(updates)
    print(f"updated meta.callee for {len(affected)} module(s)")


def rebuild_all_deps() -> None:
    """Recompute ``meta.callee`` for every module from current direct imports."""
    graph = load_dependency_graph()
    reach = compute_reach(graph)
    rows = MySQL.instance.query("SELECT module FROM lemma")
    # modules with empty imports have no graph node; their callee is [], not unknown
    updates = {m: indirect_deps(m, graph, reach) for (m,) in rows}
    batch_update_meta(updates)
    print(f"rebuilt meta.callee for {len(updates)} module(s)")


def load_deps_for(
    modules: list[str],
) -> tuple[dict[str, set[str]], dict[str, set[str]], set[str]]:
    """Load direct and indirect dependency sets scoped to the given modules.

    Returns ``(direct, indirect, unknown)``.  ``unknown`` is the set of modules
    whose ``meta.callee`` is null/absent — their indirect deps are not known, so
    they must never be treated as "no indirect deps".
    """
    if not modules:
        return {}, {}, set()
    # File-level import names are ``Lemma.``-prefixed; DB rows are not.
    originals = {normalize_module(m): m for m in modules}
    quoted = ", ".join(sql_str(m) for m in originals)

    direct_sql = (
        f"SELECT module, jt.import FROM lemma "
        f"CROSS JOIN JSON_TABLE(imports, '$[*]' "
        f"COLUMNS (import VARCHAR(256) PATH '$')) AS jt "
        f"WHERE module IN ({quoted})"
    )
    direct_rows = MySQL.instance.query(direct_sql)
    direct: dict[str, set[str]] = {}
    for module, imp in direct_rows:
        # imp keeps its raw (``Lemma.``-prefixed) form, matching file import lines
        direct.setdefault(originals[module], set()).add(imp)

    indirect_sql = (
        f"SELECT module, JSON_EXTRACT(meta, '$.callee') FROM lemma "
        f"WHERE module IN ({quoted})"
    )
    indirect_rows = MySQL.instance.query(indirect_sql)
    indirect: dict[str, set[str]] = {}
    unknown: set[str] = set()
    module_set = set(modules)
    for module, callee_json in indirect_rows:
        if callee_json is None:
            unknown.add(originals[module])
            continue
        deps = json.loads(callee_json) if isinstance(callee_json, str) else callee_json
        if deps is None:
            unknown.add(originals[module])
            continue
        if isinstance(deps, dict):
            # legacy {callee: [via, ...]} shape — the via arrays are ignored
            deps = list(deps)
        for callee in deps:
            # callee is stored unprefixed; compare against prefixed file names
            prefixed = LEMMA_PREFIX + normalize_module(callee)
            if prefixed in module_set:
                indirect.setdefault(originals[module], set()).add(prefixed)

    return direct, indirect, unknown


def compare(
    a: str,
    b: str,
    direct: dict[str, set[str]],
    indirect: dict[str, set[str]],
) -> int:
    """Return 1 if a calls b, -1 if b calls a, 0 if independent."""
    a_deps = direct.get(a, set()) | indirect.get(a, set())
    b_deps = direct.get(b, set()) | indirect.get(b, set())
    if b in a_deps:
        return 1
    if a in b_deps:
        return -1
    return 0


def find_redundant_imports(
    imports: list[tuple[str, str]],
    direct: dict[str, set[str]],
    indirect: dict[str, set[str]],
) -> list[str]:
    """Pairwise compare: n*(n-1)/2 calls to compare."""
    lemma_modules = [mod for mod, _ in imports if mod.startswith("Lemma")]
    if len(lemma_modules) <= 1:
        return []

    redundant: set[str] = set()
    for i in range(len(lemma_modules)):
        for j in range(i + 1, len(lemma_modules)):
            a = lemma_modules[i]
            b = lemma_modules[j]
            c = compare(a, b, direct, indirect)
            if c == 1:
                redundant.add(b)
            elif c == -1:
                redundant.add(a)
    return [mod for mod in lemma_modules if mod in redundant]


def update_module_after_prune(
    module: str,
    kept_imports: list[str],
    removed: list[str],
) -> None:
    """Sync the lemma row after pruning ``module``'s file.

    Reachability is unchanged (only redundant imports were removed), so callers
    need no invalidation.  ``module``'s own callee gains the removed imports:
    they are no longer direct but remain reachable.  Unknown (null) callee
    stays null; a missing row is left for run.ps1 to insert.
    """
    rows = MySQL.instance.query(
        f"SELECT JSON_EXTRACT(meta, '$.callee') FROM lemma WHERE module = {sql_str(module)}"
    )
    if not rows:
        print(f"note: {module} not in lemma table; DB update skipped "
              f"(run.ps1 will insert it)")
        return

    # compact separators + raw unicode match what run.ps1's change detection
    # expects, so it will not see a spurious imports modification
    imports_sql = sql_str(json.dumps(kept_imports, ensure_ascii=False, separators=(",", ":")))
    sets = [f"imports = {imports_sql}"]

    callee_json = rows[0][0]
    if callee_json is not None:
        deps = json.loads(callee_json) if isinstance(callee_json, str) else callee_json
        if deps is not None:
            if isinstance(deps, dict):
                # legacy {callee: [via, ...]} shape — the via arrays are ignored
                deps = list(deps)
            callee = {normalize_module(d) for d in deps}
            callee |= {normalize_module(r) for r in removed}
            sets.append(
                f"meta = JSON_SET(IFNULL(meta, '{{}}'), '$.callee', "
                f"CAST({sql_str(json.dumps(sorted(callee), ensure_ascii=False))} AS JSON))"
            )

    MySQL.instance.execute(
        f"UPDATE lemma SET {', '.join(sets)} WHERE module = {sql_str(module)}"
    )
    print(f"updated lemma row for {module} (imports, meta.callee)")


def process_file(lean_file: Path, *, dry_run: bool = False) -> None:
    content = read_text(lean_file)
    rel = rel_path_for(lean_file)
    imports, rest = parse_import_block(content)

    lemma_modules = [mod for mod, _ in imports if mod.startswith("Lemma")]
    print(f"checking {len(lemma_modules)} Lemma imports for {rel} ...")

    direct, indirect, unknown = load_deps_for(lemma_modules)
    if unknown:
        print(f"warning: {len(unknown)} import(s) have unknown meta.callee "
              f"(run --update first); indirect checks skipped for them")
        for mod in unknown:
            print(f"  {mod}")
    redundant = find_redundant_imports(imports, direct, indirect)

    if not redundant:
        print("imports ok: no redundant Lemma imports")
        return

    print("redundant imports:")
    for mod in redundant:
        print(f"  import {mod}")

    if dry_run:
        print(f"dry-run: would remove {len(redundant)} import(s) from {rel}")
        return

    redundant_set = set(redundant)
    kept = [(mod, line) for mod, line in imports if mod not in redundant_set]
    new_content = "".join(line for _, line in kept) + rest
    write_text(lean_file, new_content)
    print(f"removed {len(redundant)} import(s) from {rel}")

    db_module = normalize_module(rel[:-len(".lean")].replace("/", "."))
    update_module_after_prune(db_module, [mod for mod, _ in kept], redundant)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Delete unnecessary Lemma imports from a .lean file (meta.callee in lemma table).",
    )
    parser.add_argument(
        "lean_file",
        nargs="?",
        help="path to a .lean file (e.g. Lemma/Real/SomeLemma.lean)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="analyze but do not write the file",
    )
    parser.add_argument(
        "--update",
        metavar="MODULE",
        help="incrementally update meta.callee for a changed module and its callers",
    )
    parser.add_argument(
        "--rebuild",
        action="store_true",
        help="recompute meta.callee for every module from current direct imports",
    )
    args = parser.parse_args()

    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")

    if args.rebuild:
        rebuild_all_deps()
        return

    if args.update:
        update_lemma_dep(args.update)
        return

    lean_file_arg = args.lean_file
    if not lean_file_arg:
        lean_file_arg = input("Lean file path: ").strip()
    if not lean_file_arg:
        parser.error("no lean file provided")

    lean_file = Path(lean_file_arg)
    if not lean_file.is_absolute():
        lean_file = ROOT / lean_file
    lean_file = lean_file.resolve()

    if not lean_file.exists():
        parser.error(f"file not found: {lean_file}")

    process_file(lean_file, dry_run=args.dry_run)


if __name__ == "__main__":
    main()
