"""
topo_sort.py
============

Project-agnostic topological sort of every lemma/theorem in a Lean
formalisation.  Generalises ``flt_topo_sort.py`` to handle arbitrary
project layouts.

Two built-in profiles via flags:

  FLT  : --source-subpath P2M/Sol --file-prefix S_ \\
         --dep-filter '^Theorems\\.Thm_(\\w+)$' --root fermat_last_theorem

  ATLAS: --source-subpath MathlibExt --recursive \\
         (no file prefix, no dep filter, no root)

Node identity
-------------
  - With ``--file-prefix PREFIX``: node = filename minus PREFIX and ``.lean``
    (preserves the FLT ``<key>`` convention so ``flt_topo_sort.log`` format
    is reproducible).
  - Without ``--file-prefix``:     node = Lean module name
    (e.g. ``MathlibExt.Probability.BerryEsseen``).

Dependency parsing
------------------
  - Read ``import X.Y.Z`` lines from each file header.
  - With ``--dep-filter REGEX``:   keep only imports matching REGEX,
    ``group(1)`` is the dep ID (must match an in-tree node).
  - Without ``--dep-filter``:      keep imports whose target module is
    itself a discovered node (in-tree filter).

Already-ported detection
------------------------
  - With ``--ported-regex REGEX``: scan every ``.lean`` under
    ``--ported-root``; ``group(1)`` of each match is a ported node ID.
  - Without it: no ported detection (every node is a candidate).

Output
------
The first ``--limit`` ready-to-port nodes (deps all ported, mutually
independent) are written to the ``.log`` file and echoed to stdout.
Each entry is a Markdown link ``[node](<base_url>/<relative_path>.lean)``.
"""

from __future__ import annotations

import argparse
import heapq
import os
import re
import sys
import time

DEFAULT_LIMIT = 20


def list_files(base: str, source_subpath: str, file_prefix: str,
               recursive: bool) -> tuple[list[tuple[str, str, str]], str]:
    """Return ``[(node_id, abs_path, rel_path_posix), ...]`` and the walked root.

    ``rel_path`` is always POSIX (forward slashes) so it can be appended
    to a GitHub base URL verbatim.
    """
    root = os.path.join(base, source_subpath) if source_subpath else base
    out: list[tuple[str, str, str]] = []

    def emit(abs_path: str) -> None:
        rel = os.path.relpath(abs_path, base).replace(os.sep, "/")
        name = os.path.basename(abs_path)
        if file_prefix:
            if not name.startswith(file_prefix):
                return
            node_id = name[len(file_prefix):-len(".lean")]
        else:
            # Module name: rel path without extension, / -> .
            node_id = rel[:-len(".lean")].replace("/", ".")
        out.append((node_id, abs_path, rel))

    if recursive:
        for dp, dn, fn in os.walk(root):
            # Skip VCS / build dirs.
            dn[:] = [d for d in dn if d not in (".lake", ".git", "_target")]
            for name in fn:
                if name.endswith(".lean"):
                    emit(os.path.join(dp, name))
    else:
        for name in os.listdir(root):
            if name.endswith(".lean"):
                emit(os.path.join(root, name))
    return out, root


def read_dependencies(abs_path: str, dep_filter_re, in_tree_ids: set[str]) -> list[str]:
    """Parse ``import X.Y.Z`` (and ``public import X.Y.Z``) lines from the
    file header.  Return in-tree deps.

    Skips leading boilerplate (multi-line ``/- ... -/`` block comments,
    ``--`` line comments, the ``module`` keyword, blank lines) before the
    first import.  Once at least one import has been seen, the next
    non-import line ends the import block.
    """
    deps: list[str] = []
    in_block_comment = False
    seen_import = False
    with open(abs_path, "r", encoding="utf-8", errors="replace") as f:
        for line in f:
            s = line.strip()
            if in_block_comment:
                if s.endswith("-/"):
                    in_block_comment = False
                continue
            if not s:
                continue
            if s.startswith("/-"):
                # Single-line ``/- ... -/`` or multi-line block opener.
                if not s.endswith("-/"):
                    in_block_comment = True
                continue
            if s.startswith("--"):
                continue
            # Both `import X` and `public import X` count.
            if s.startswith("import "):
                tokens = s[len("import "):].split()
            elif s.startswith("public import "):
                tokens = s[len("public import "):].split()
            else:
                # Before any import: skip (module decl, namespace, etc.).
                # After at least one import: end of header.
                if seen_import:
                    break
                continue
            seen_import = True
            for tok in tokens:
                if dep_filter_re:
                    m = dep_filter_re.match(tok)
                    if m and m.group(1) in in_tree_ids:
                        deps.append(m.group(1))
                else:
                    if tok in in_tree_ids:
                        deps.append(tok)
    return deps


def has_sorry(abs_path: str) -> bool:
    """Return True if the file uses ``sorry`` as a tactic.

    Strips ``/- ... -/`` block comments and ``--`` line comments first,
    so the word ``sorry`` in prose (docstrings, comments) does not count.
    Matches ``sorry`` as a word (``\\bsorry\\b``) so identifiers like
    ``sorryFree`` or ``no_sorry`` are not flagged.
    """
    in_block_comment = False
    with open(abs_path, "r", encoding="utf-8", errors="replace") as f:
        for line in f:
            s = line.strip()
            if in_block_comment:
                if s.endswith("-/"):
                    in_block_comment = False
                continue
            if s.startswith("/-"):
                if not s.endswith("-/"):
                    in_block_comment = True
                continue
            if s.startswith("--"):
                continue
            if re.search(r"\bsorry\b", s):
                return True
    return False


def topological_sort(keys: list[str], deps_of: dict[str, list[str]]):
    """Kahn's algorithm.  Returns ``(order, rank, acyclic)``.

    ``rank`` is the length of the longest prerequisite chain ending at a
    node (leaves are 0).  Heap is keyed by node name for deterministic
    lexicographic tie-break.
    """
    dependents: dict[str, list[str]] = {k: [] for k in keys}
    for k, deps in deps_of.items():
        for d in deps:
            dependents[d].append(k)

    indeg = {k: len(deps_of[k]) for k in keys}
    rank = {k: 0 for k in keys}

    heap = [(k, k) for k in keys if indeg[k] == 0]
    heapq.heapify(heap)

    order: list[str] = []
    while heap:
        _, u = heapq.heappop(heap)
        order.append(u)
        for v in dependents[u]:
            if rank[u] + 1 > rank[v]:
                rank[v] = rank[u] + 1
            indeg[v] -= 1
            if indeg[v] == 0:
                heapq.heappush(heap, (v, v))

    acyclic = len(order) == len(keys)
    return order, rank, acyclic


def ported_keys(ported_root: str, ported_re) -> set[str]:
    """Return node IDs already ported, by scanning ``.lean`` files under
    ``ported_root`` for ``ported_re`` matches (``group(1)``).
    """
    keys: set[str] = set()
    if not ported_root or not os.path.isdir(ported_root):
        return keys
    for dp, dn, fn in os.walk(ported_root):
        dn[:] = [d for d in dn if d not in (".lake", ".git", "_target")]
        for name in fn:
            if not name.endswith(".lean"):
                continue
            try:
                with open(os.path.join(dp, name), "r",
                          encoding="utf-8", errors="replace") as f:
                    text = f.read()
            except OSError:
                continue
            for m in ported_re.finditer(text):
                raw = m.group(1)
                # Normalize path-style captures (ATLAS: 'MathlibExt/Probability/X')
                # to module-name form ('MathlibExt.Probability.X') so they
                # match in-tree node IDs.  FLT keys have no '/' so this is
                # a no-op for them.
                if raw.endswith(".lean"):
                    raw = raw[:-len(".lean")]
                keys.add(raw.replace("/", "."))
    return keys


def build_summary(base: str, root: str, n_nodes: int, n_edges: int,
                  max_rank: int, acyclic: bool, secs: float,
                  n_ported: int, n_out: int, n_sorry: int = 0) -> str:
    root_line = (f"root    : {root} (pinned last)" if root
                 else "root    : (none — library graph)")
    lines = [
        "=" * 80,
        "Topological sort of lemmas/theorems",
        f"project : {base}",
        "order   : simplest first, most complex last",
        root_line,
        "-" * 80,
        f"nodes             : {n_nodes}",
        f"edges (imports)   : {n_edges}",
        f"max depth (rank)  : {max_rank}",
        f"acyclic           : {acyclic}",
        f"already ported    : {n_ported} (excluded)",
    ]
    if n_sorry:
        lines.append(f"sorry-containing  : {n_sorry} (excluded by --no-sorry)")
    lines += [
        f"listed            : {n_out} (independent batch)",
        f"elapsed           : {secs:.2f}s",
        "-" * 80,
    ]
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Project-agnostic topological sort of Lean proofs.")
    ap.add_argument("--base", required=True,
                    help="Project root (e.g. /mnt/e/github/atlas-lean).")
    ap.add_argument("--source-subpath", default="",
                    help="Subdir within --base containing source files "
                         "(e.g. 'P2M/Sol' for FLT, 'MathlibExt' for ATLAS).")
    ap.add_argument("--file-prefix", default="",
                    help="Filename prefix to strip when forming node IDs "
                         "(e.g. 'S_' for FLT). Empty => use full module name.")
    ap.add_argument("--recursive", action="store_true",
                    help="Walk source subdir recursively (ATLAS). "
                         "Off => only top-level files (FLT's P2M/Sol).")
    ap.add_argument("--dep-filter", default="",
                    help="Regex applied to each import token; group(1) is "
                         "the dep ID. FLT uses '^Theorems\\.Thm_(\\w+)$'. "
                         "Empty => use the raw module path as dep ID.")
    ap.add_argument("--root", default="",
                    help="Node to pin last (FLT: 'fermat_last_theorem'). "
                         "Empty => no pinning (ATLAS).")
    ap.add_argument("--base-url", required=True,
                    help="GitHub base URL for source links, e.g. "
                         "https://github.com/facebookresearch/atlas-lean/blob/main")
    ap.add_argument("--ported-root", default="",
                    help="Directory scanned for already-ported lemmas "
                         "(e.g. your Lemma/ tree).")
    ap.add_argument("--ported-regex", default="",
                    help="Regex to extract ported node ID from .lean content. "
                         "group(1) must equal the in-tree node ID.")
    ap.add_argument("--limit", type=int, default=DEFAULT_LIMIT,
                    help="How many ready, mutually-independent nodes to list.")
    ap.add_argument("--no-sorry", action="store_true",
                    help="Exclude files containing `sorry` as a tactic from "
                         "the candidate batch (their own proof must be "
                         "complete). Transitive sorry deps are OK — the "
                         "candidate only relies on the dep's statement.")
    ap.add_argument("--out", default=None,
                    help="Path of the .log file (default: alongside this script).")
    args = ap.parse_args()

    t0 = time.time()

    files, _ = list_files(args.base, args.source_subpath,
                          args.file_prefix, args.recursive)
    in_tree_ids = {nid for nid, _, _ in files}
    path_of = {nid: rel for nid, _, rel in files}

    if not in_tree_ids:
        print(f"ERROR: no .lean files found under "
              f"{os.path.join(args.base, args.source_subpath)}", file=sys.stderr)
        return 1

    dep_filter_re = re.compile(args.dep_filter) if args.dep_filter else None
    deps_of = {nid: read_dependencies(abs_path, dep_filter_re, in_tree_ids)
               for nid, abs_path, _ in files}
    n_edges = sum(len(d) for d in deps_of.values())

    order, rank, acyclic = topological_sort(list(in_tree_ids), deps_of)

    if not acyclic:
        print("ERROR: dependency graph contains a cycle.", file=sys.stderr)

    ported_re = re.compile(args.ported_regex) if args.ported_regex else None
    ported = ported_keys(args.ported_root, ported_re) if ported_re else set()

    # Files whose own proof is incomplete (contain `sorry` as a tactic).
    # Only computed when --no-sorry is set.  These files stay in the graph
    # (they may be deps of clean files) but are excluded from the candidate
    # batch — we only port fully-proved theorems.
    sorry_files: set[str] = set()
    if args.no_sorry:
        for nid, abs_path, _ in files:
            if has_sorry(abs_path):
                sorry_files.add(nid)

    # Simplest -> most complex: rank ascending, then lexicographic.
    final = sorted(in_tree_ids, key=lambda k: (rank[k], k))

    if args.root:
        if args.root in final:
            final.remove(args.root)
            final.append(args.root)
        else:
            print(f"WARNING: root '{args.root}' not found among nodes.",
                  file=sys.stderr)

    # Ready batch: deps already ported (or none), own proof sorry-free.
    # Mutually independent because a ready node's deps are all ported,
    # hence not in this batch.
    batch: list[str] = []
    for k in final:
        if k in ported:
            continue
        if k in sorry_files:
            continue
        if all(d in ported for d in deps_of[k]):
            batch.append(k)
            if len(batch) >= args.limit:
                break

    max_rank = max(rank.values()) if rank else 0
    secs = time.time() - t0

    header = build_summary(args.base, args.root, len(in_tree_ids), n_edges,
                           max_rank, acyclic, secs,
                           len(ported), len(batch),
                           n_sorry=len(sorry_files))

    body_lines = [f"[{k}]({args.base_url}/{path_of[k]})" for k in batch]
    out_text = header + "\n\n" + "\n".join(body_lines) + "\n"

    out = args.out
    if out is None:
        out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "topo_sort.log")

    with open(out, "w", encoding="utf-8") as f:
        f.write(out_text)

    print(header)
    print()
    for line in body_lines:
        print(line)
    print(f"\nLog written to: {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
