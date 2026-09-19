"""
flt_topo_sort.py
================

Topological sort of every lemma/theorem in the ``fermats-last-theorem``
formalisation (E:\\github\\lean\\fermats-last-theorem).

How the dependency graph is read
--------------------------------
Per ``PROOF-PATH.md``: a theorem ``X.y`` is *stated* in
``Theorems/Thm_X_y.lean`` and *proved* in ``P2M/Sol/S_X_y.lean``, and the
``import Theorems.Thm_…`` lines of the solution file are exactly the theorems
it cites.

So we take one node per ``S_<key>.lean`` file (the ``<key>`` between ``S_`` and
``.lean``), read the ``import Theorems.Thm_…`` lines out of its header, and
treat those as "prerequisites".  ``<key>`` is therefore a canonical, unique
identifier of the theorem: it maps back to ``Theorems/Thm_<key>.lean`` and
``P2M/Sol/S_<key>.lean``.

Ordering
--------
"Simplest first, most complex last" is realised by ranking each node with the
length of its *longest prerequisite chain* (a leaf has rank 0), then sorting by
rank ascending (ties broken lexicographically).  This is always a valid
topological order, because a prerequisite always has strictly smaller rank than
its dependent.  The root theorem (``fermat_last_theorem``) is pinned to the very
last position as requested.

Output
------
Only the first ``--limit`` theorems that are ready to port (all their FLT
prerequisites are already ported) are written to the ``.log`` file and echoed
to stdout.  Ready theorems never reference one another, so agents can process
them simultaneously without conflicts.  Each entry is a Markdown link whose
text is the theorem key and whose target is the theorem's proof file on GitHub
(``P2M/Sol/S_<key>.lean``).  Theorems already ported (detected by scanning the
``Lemma`` tree for their source link) are excluded.

Note: some theorem file names exceed Windows' 260-character ``MAX_PATH`` limit,
so every file is opened through the ``\\\\?\\`` extended-length path prefix.
"""

from __future__ import annotations

import argparse
import heapq
import os
import re
import sys
import time

DEFAULT_BASE = r"E:\github\lean\fermats-last-theorem"
DEFAULT_ROOT = "fermat_last_theorem"
DEFAULT_BASE_URL = "https://github.com/anthropics/fermats-last-theorem/blob/main"
DEFAULT_PORTED_ROOT = r"E:\github\lean\Lemma"
DEFAULT_LIMIT = 20

# A ported theorem's file carries a doc comment linking back to its FLT source,
# e.g.  [Key](https://github.com/.../P2M/Sol/S_Key.lean) - capture the Key.
PORTED_RE = re.compile(r"P2M/Sol/S_([A-Za-z0-9_]+)\.lean")


def ext_path(path: str) -> str:
    """Return the ``\\\\?\\``-prefixed path so long names open on Windows."""
    # Avoid double-prefixing.
    return path if path.startswith("\\\\?\\") else "\\\\?\\" + path


def list_keys(directory: str, prefix: str) -> list[str]:
    """Return the ``<key>`` part of every ``<prefix><key>.lean`` file."""
    keys = []
    for name in os.listdir(directory):
        if name.startswith(prefix) and name.endswith(".lean"):
            keys.append(name[len(prefix):-len(".lean")])
    return keys


def read_dependencies(key: str, sol_dir: str) -> list[str]:
    """Read the header of ``S_<key>.lean`` and return its theorem prerequisites."""
    path = ext_path(os.path.join(sol_dir, "S_" + key + ".lean"))
    deps: list[str] = []
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        for line in f:
            s = line.strip()
            if not s or s.startswith("--") or s.startswith("/-"):
                continue
            if s.startswith("import "):
                for tok in s[len("import "):].split():
                    if tok.startswith("Theorems.Thm_"):
                        deps.append(tok[len("Theorems.Thm_"):])
            else:
                # Lean imports always precede any real content: we are done.
                break
    return deps


def ported_keys(ported_root: str) -> set[str]:
    """Return the FLT theorem keys that have already been ported.

    A ported theorem's file carries a doc comment linking back to its FLT
    source, e.g. ``[Key](.../P2M/Sol/S_Key.lean)``.  Scan every ``.lean`` file
    under ``ported_root`` and collect the ``Key`` inside that link.
    """
    keys: set[str] = set()
    if not os.path.isdir(ported_root):
        return keys
    for dirpath, dirnames, filenames in os.walk(ported_root):
        dirnames[:] = [d for d in dirnames if d not in (".lake", ".git")]
        for name in filenames:
            if not name.endswith(".lean"):
                continue
            try:
                with open(ext_path(os.path.join(dirpath, name)),
                          "r", encoding="utf-8", errors="replace") as f:
                    text = f.read()
            except OSError:
                continue
            for m in PORTED_RE.finditer(text):
                keys.add(m.group(1))
    return keys


def topological_sort(keys: list[str], deps_of: dict[str, list[str]]):
    """Kahn's algorithm.  Returns ``(order, rank, acyclic)``.

    ``rank`` is the length of the longest prerequisite chain ending at a node
    (leaves are 0), computed on the fly while the queue drains.
    """
    dependents: dict[str, list[str]] = {k: [] for k in keys}
    for k, deps in deps_of.items():
        for d in deps:
            dependents[d].append(k)

    indeg = {k: len(deps_of[k]) for k in keys}
    rank = {k: 0 for k in keys}

    # Heap keyed by (name, name): deterministic lexicographic tie-break.
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


def build_summary(base: str, root: str, n_nodes: int, n_edges: int,
                  max_rank: int, acyclic: bool, secs: float,
                  n_ported: int, n_out: int) -> str:
    lines = [
        "=" * 80,
        "Topological sort of lemmas/theorems",
        f"project : {base}",
        f"order   : simplest first, most complex last",
        f"root    : {root} (pinned last)",
        "-" * 80,
        f"nodes             : {n_nodes}",
        f"edges (imports)   : {n_edges}",
        f"max depth (rank)  : {max_rank}",
        f"acyclic           : {acyclic}",
        f"already ported    : {n_ported} (excluded)",
        f"listed            : {n_out} (independent batch)",
        f"elapsed           : {secs:.2f}s",
        "-" * 80,
    ]
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(description="Topological sort of the FLT proof tree.")
    ap.add_argument("--base", default=DEFAULT_BASE,
                    help="Root of the fermats-last-theorem project.")
    ap.add_argument("--root", default=DEFAULT_ROOT,
                    help="Theorem that must appear last.")
    ap.add_argument("--out", default=None,
                    help="Path of the .log file (default: alongside this script).")
    ap.add_argument("--base-url", default=DEFAULT_BASE_URL,
                    help="GitHub base URL used to link each theorem to its proof file.")
    ap.add_argument("--ported-root", default=DEFAULT_PORTED_ROOT,
                    help="Directory scanned for already-ported theorems (Lemma tree).")
    ap.add_argument("--limit", type=int, default=DEFAULT_LIMIT,
                    help="How many ready, mutually-independent theorems to list.")
    args = ap.parse_args()

    base = args.base
    root = args.root
    sol_dir = os.path.join(base, "P2M", "Sol")

    t0 = time.time()

    keys = sorted(list_keys(sol_dir, "S_"))
    deps_of = {k: read_dependencies(k, sol_dir) for k in keys}

    # Keep only prerequisites that actually have a node (defensive: imports to
    # modules outside the theorem tree are ignored).
    key_set = set(keys)
    n_edges = 0
    for k in keys:
        deps_of[k] = [d for d in deps_of[k] if d in key_set]
        n_edges += len(deps_of[k])

    order, rank, acyclic = topological_sort(keys, deps_of)

    if not acyclic:
        print("ERROR: dependency graph contains a cycle.", file=sys.stderr)

    # Already-ported theorems: found by scanning the Lemma tree for a link back
    # to their FLT source file.
    ported = ported_keys(args.ported_root)

    # Simplest -> most complex: rank ascending, then lexicographic.
    final = sorted(keys, key=lambda k: (rank[k], k))

    # Pin the root theorem to the very last position.
    if root in final:
        final.remove(root)
        final.append(root)
    else:
        print(f"WARNING: root theorem '{root}' not found among nodes.",
              file=sys.stderr)

    # Keep only the first --limit unported theorems that are ready to port
    # (every FLT prerequisite already ported).  Such theorems never reference
    # one another, so agents can process them simultaneously without conflicts.
    batch = []
    for k in final:
        if k in ported:
            continue
        if all(d in ported for d in deps_of[k]):
            batch.append(k)
            if len(batch) >= args.limit:
                break

    max_rank = max(rank.values()) if rank else 0
    secs = time.time() - t0

    header = build_summary(base, root, len(keys), n_edges, max_rank, acyclic, secs,
                           len(ported), len(batch))

    body_lines = [f"[{k}]({args.base_url}/P2M/Sol/S_{k}.lean)" for k in batch]
    out_text = header + "\n\n" + "\n".join(body_lines) + "\n"

    # Where to write the log.
    out = args.out
    if out is None:
        out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "flt_topo_sort.log")

    with open(out, "w", encoding="utf-8") as f:
        f.write(out_text)

    # Echo to stdout as requested.
    print(header)
    print()
    for line in body_lines:
        print(line)
    print(f"\nLog written to: {out}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
