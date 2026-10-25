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

import sys
from pathlib import Path

# `python3 py/delete_import.py` puts this script's directory on sys.path[0],
# which shadows the stdlib ``http`` package with ``py/http.py`` (breaks
# mysql.connector). Prefer the repo root as the import root.
ROOT = Path(__file__).resolve().parents[1]
_SCRIPT_DIR = Path(__file__).resolve().parent
_script_dir = str(_SCRIPT_DIR)
while _script_dir in sys.path:
    sys.path.remove(_script_dir)
_root = str(ROOT)
if _root not in sys.path:
    sys.path.insert(0, _root)

import os
os.environ['MYSQL_DATABASE'] = 'axiom'
import py
from py import MySQL

import argparse
import json
import re
from collections.abc import Iterable

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
    whose ``meta.callee`` is null/absent — their transitive deps are incomplete,
    so they must not be used as the sole reason to drop sibling imports.
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
    seen_meta: set[str] = set()
    module_set = set(modules)
    for module, callee_json in indirect_rows:
        orig = originals[module]
        seen_meta.add(orig)
        if callee_json is None:
            unknown.add(orig)
            continue
        deps = json.loads(callee_json) if isinstance(callee_json, str) else callee_json
        if deps is None:
            unknown.add(orig)
            continue
        if isinstance(deps, dict):
            # legacy {callee: [via, ...]} shape — the via arrays are ignored
            deps = list(deps)
        for callee in deps:
            # callee is stored unprefixed; compare against prefixed file names
            prefixed = LEMMA_PREFIX + normalize_module(callee)
            if prefixed in module_set:
                indirect.setdefault(orig, set()).add(prefixed)

    # Missing lemma rows: treat like unknown meta.callee.
    for m in modules:
        if m not in seen_meta:
            unknown.add(m)

    return direct, indirect, unknown


def enrich_unknown_from_files(
    modules: list[str],
    direct: dict[str, set[str]],
    indirect: dict[str, set[str]],
    unknown: set[str],
) -> None:
    """For imports with unknown ``meta.callee``, fill sibling reachability from files.

    DB null callee must not be read as "no transitive deps" (that falsely marks
    siblings redundant when paired with incomplete data).  File closures among
    the current import set are a safe stand-in; they never invent edges that are
    not on disk.
    """
    module_set = set(modules)
    for u in unknown:
        # Prefer DB direct edges when present; also scan the .lean file.
        for dep in file_direct_imports(u):
            if dep in module_set and dep != u:
                direct.setdefault(u, set()).add(dep)
        for dep in file_closure(u):
            if dep in module_set and dep != u and dep not in direct.get(u, ()):
                indirect.setdefault(u, set()).add(dep)


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


def import_name_used_in_body(module: str, body: str) -> bool:
    """True if ``module``'s lemma path appears in ``body`` (non-import text).

    ``Lemma.Matrix.Foo.eq.Bar`` is referenced in proofs as ``Matrix.Foo.eq.Bar``
    or, after ``open``/section elision, ``Foo.eq.Bar``.  Used imports must never
    be dropped even when another import transitively reaches them in the DB.
    """
    bare = normalize_module(module)
    if bare and bare in body:
        return True
    parts = bare.split(".")
    if len(parts) >= 2:
        short = ".".join(parts[1:])
        if short and short in body:
            return True
    return False


_FILE_IMPORTS: dict[str, list[str]] = {}


def file_direct_imports(module: str) -> list[str]:
    """Direct ``import`` lines of a repo-local module (``Lemma.*``, ``sympy.*``, ``stdlib.*``),
    parsed from its ``.lean`` file.  Modules without a file here (e.g. ``Mathlib.*``) are leaves."""
    if module not in _FILE_IMPORTS:
        deps: list[str] = []
        path = ROOT / (module.replace(".", "/") + ".lean")
        if path.is_file():
            for line in read_text(path).split("\n"):
                match = IMPORT_LINE_RE.match(line)
                if match:
                    deps.append(match.group(1))
                elif line.strip() and not line.startswith("--"):
                    break
        _FILE_IMPORTS[module] = deps
    return _FILE_IMPORTS[module]


def file_closure(module: str) -> set[str]:
    """Transitive imports of ``module`` computed from the ``.lean`` files (no database)."""
    seen: set[str] = set()
    stack = [module]
    while stack:
        for dep in file_direct_imports(stack.pop()):
            if dep not in seen:
                seen.add(dep)
                stack.append(dep)
    return seen


def find_redundant_file_imports(imports: list[tuple[str, str]]) -> list[str]:
    """Redundant imports among pairs that involve a non-``Lemma`` (``sympy.*``) import.

    ``sympy.*`` modules have no ``lemma`` row, so reachability is read from the ``.lean`` files:
    a ``Lemma.*`` or ``sympy.*`` import is redundant when another import of the file reaches it.
    ``Lemma.*`` / ``Lemma.*`` pairs stay with ``find_redundant_imports`` (database)."""
    modules = list(dict.fromkeys(mod for mod, _ in imports))
    closures: dict[str, set[str]] = {}
    redundant: set[str] = set()
    for b in modules:
        if not (b.startswith("sympy.") or b.startswith("Lemma")):
            continue
        for a in modules:
            if a == b or (a.startswith("Lemma") and b.startswith("Lemma")):
                continue
            if a not in closures:
                closures[a] = file_closure(a)
            if b in closures[a]:
                redundant.add(b)
                break
    return [mod for mod in modules if mod in redundant]


def find_redundant_imports(
    imports: list[tuple[str, str]],
    direct: dict[str, set[str]],
    indirect: dict[str, set[str]],
    unknown: set[str] | None = None,
) -> list[str]:
    """Pairwise compare: n*(n-1)/2 calls to compare.

    An import with unknown ``meta.callee`` must not drop a sibling solely via
    incomplete transitive data.  Only a *known* reacher (or a direct edge) may
    mark the other side redundant; if the reacher is still in ``unknown`` after
    file enrichment, skip that direction.
    """
    lemma_modules = [mod for mod, _ in imports if mod.startswith("Lemma")]
    if len(lemma_modules) <= 1:
        return []
    unknown = unknown or set()

    redundant: set[str] = set()
    for i in range(len(lemma_modules)):
        for j in range(i + 1, len(lemma_modules)):
            a = lemma_modules[i]
            b = lemma_modules[j]
            c = compare(a, b, direct, indirect)
            if c == 1:
                # a reaches b → b candidate redundant
                if a in unknown and b not in direct.get(a, set()):
                    continue
                redundant.add(b)
            elif c == -1:
                if b in unknown and a not in direct.get(b, set()):
                    continue
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
    rows = list(MySQL.instance.query(
        f"SELECT JSON_EXTRACT(meta, '$.callee') FROM lemma WHERE module = {sql_str(module)}"
    ))
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
    print(f"checking {len(lemma_modules)} Lemma imports for {rel} ...", flush=True)

    direct, indirect, unknown = load_deps_for(lemma_modules)
    if unknown:
        print(f"warning: {len(unknown)} import(s) have unknown meta.callee "
              f"(run --update first); using file-closure for those, and not "
              f"dropping siblings on incomplete transitive data")
        for mod in unknown:
            print(f"  {mod}")
        enrich_unknown_from_files(lemma_modules, direct, indirect, unknown)
    redundant = find_redundant_imports(imports, direct, indirect, unknown)
    redundant += [m for m in find_redundant_file_imports(imports) if m not in redundant]
    # Never drop an import still named in the proof/body (DB reachability ≠ use).
    kept_used = [m for m in redundant if import_name_used_in_body(m, rest)]
    if kept_used:
        print(f"note: keeping {len(kept_used)} reachable import(s) still referenced "
              f"in the file body:")
        for mod in kept_used:
            print(f"  import {mod}")
        redundant = [m for m in redundant if m not in set(kept_used)]
    names = [mod for mod, _ in imports]
    duplicates = sorted({m for m in names if names.count(m) > 1} - set(redundant))

    if not redundant and not duplicates:
        print("imports ok: no redundant imports")
        return

    print("redundant imports:")
    for mod in redundant:
        print(f"  import {mod}")
    for mod in duplicates:
        print(f"  import {mod}  (duplicate)")

    if dry_run:
        print(f"dry-run: would remove {len(redundant) + len(duplicates)} import(s) from {rel}")
        return

    redundant_set = set(redundant)
    kept = []
    seen_mods: set[str] = set()
    for mod, line in imports:
        if mod in redundant_set or mod in seen_mods:
            continue
        seen_mods.add(mod)
        kept.append((mod, line))
    new_content = "".join(line for _, line in kept) + rest
    write_text(lean_file, new_content)
    print(f"removed {len(imports) - len(kept)} import(s) from {rel}")

    db_module = normalize_module(rel[:-len(".lean")].replace("/", "."))
    update_module_after_prune(db_module, [mod for mod, _ in kept], redundant)


def _run_with_mysql(action, *, dry_run: bool = False) -> None:
    """Run a DB-backed action; surface connect failures clearly (no assert dump)."""
    try:
        action()
    except RuntimeError as err:
        msg = str(err)
        if "MySQL connect failed" not in msg:
            raise
        print(f"error: {msg}", file=sys.stderr)
        if dry_run:
            print(
                "dry-run: cannot analyze Lemma imports without MySQL "
                "(file left unchanged)",
                file=sys.stderr,
            )
        sys.exit(1)


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
        _run_with_mysql(rebuild_all_deps)
        return

    if args.update:
        _run_with_mysql(lambda: update_lemma_dep(args.update))
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

    _run_with_mysql(
        lambda: process_file(lean_file, dry_run=args.dry_run),
        dry_run=args.dry_run,
    )


if __name__ == "__main__":
    main()
