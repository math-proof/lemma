"""
topo_sort.py
============

Project-agnostic topological sort of every lemma/theorem in a Lean
formalisation.  Handles arbitrary project layouts via flags (replaces the
old FLT-only ``flt_topo_sort.py``).

Typical inputs
--------------
1. A **local git checkout** (``--base``).  The GitHub URL used for
   docstring links is inferred from that checkout's ``.git/config``
   (``remote "origin"`` url) and the current branch.  A bare
   ``https://github.com/org/repo`` remote becomes
   ``https://github.com/org/repo/blob/<branch>``.
2. A ``--file-regex`` that selects which ``.lean`` files are theorems to
   port and extracts their **theorem title** (node ID) from ``group(1)``.
   The title is *not* the lemma path — it is the display name used in the
   emitted ``[title](url)`` line (ready to drop into a Lean docstring).
3. Optionally ``--base-url`` to override the inferred GitHub URL.

Profiles via flags
------------------
  FLT (preferred, --file-regex; URL inferred from --base's .git/config):
         --base ~/github/fermats-last-theorem \
         --source-subpath P2M/Sol --file-regex '^S_(.+)\.lean$' --recursive \
         --dep-filter '^Theorems\.Thm_(\w+)$' --root fermat_last_theorem

  FLT (legacy --file-prefix, still supported):
         --base ~/github/fermats-last-theorem \
         --source-subpath P2M/Sol --file-prefix S_ \
         --dep-filter '^Theorems\.Thm_(\w+)$' --root fermat_last_theorem

  ATLAS: --base ~/github/atlas-lean \
         --source-subpath MathlibExt --recursive \
         (no file prefix / regex, no dep filter, no root)

Node identity / theorem title
-----------------------------
  - With ``--file-regex REGEX``: for each ``.lean`` file, try REGEX against
    (1) the relative POSIX path, (2) the basename, then (3) the file
    contents.  The first match wins; ``group(1)`` is the theorem title
    (node ID).  ``--file-prefix`` is ignored.
    Example: ``'^S_(.+)\.lean$'`` reproduces the FLT ``<key>`` convention
    via the basename match.
  - With ``--file-prefix PREFIX`` (and no ``--file-regex``):
    title = filename minus PREFIX and ``.lean``.
  - Without either: title = Lean module name
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
Each entry is a Markdown link ``[title](<base_url>/<relative_path>.lean)``
suitable as a Lean docstring source attribution.
"""

from __future__ import annotations

import argparse
import heapq
import os
import re
import subprocess
import sys
import time

DEFAULT_BASE = "~/github/fermats-last-theorem"
DEFAULT_PORTED_ROOT = "~/github/lean/Lemma"
DEFAULT_LIMIT = 20


def normalize_base_url(url: str, default_ref: str = "main") -> str:
    """Turn a GitHub repo URL into a ``.../blob/<ref>`` base for file links.

    Already-qualified blob/tree URLs are returned unchanged (trailing slash
    stripped).  Bare ``https://github.com/org/repo`` URLs gain
    ``/blob/<default_ref>``.
    """
    u = url.rstrip("/")
    if re.search(r"/blob/[^/]+(/|$)", u) or re.search(r"/tree/[^/]+(/|$)", u):
        return u
    # Strip a trailing .git if present.
    if u.endswith(".git"):
        u = u[:-4]
    return f"{u}/blob/{default_ref}"


def remote_url_to_https(remote: str) -> str:
    """Convert a git remote URL to an ``https://host/org/repo`` web URL.

    Handles ``git@host:org/repo.git``, ``ssh://git@host/org/repo.git``,
    and ``https://host/org/repo.git``.  Strips a trailing ``.git``.
    """
    u = remote.strip().rstrip("/")
    if u.endswith(".git"):
        u = u[:-4]
    # git@host:org/repo
    m = re.match(r"^git@([^:]+):(.+)$", u)
    if m:
        return f"https://{m.group(1)}/{m.group(2).lstrip('/')}"
    # ssh://git@host/org/repo  or  ssh://host/org/repo
    m = re.match(r"^ssh://(?:git@)?([^/]+)/(.+)$", u)
    if m:
        return f"https://{m.group(1)}/{m.group(2).lstrip('/')}"
    # https://... already
    if u.startswith("http://") or u.startswith("https://"):
        return u
    raise ValueError(f"unrecognised git remote URL: {remote!r}")


def _git(base: str, *args: str) -> str | None:
    """Run ``git -C <base> …``; return stripped stdout or ``None`` on failure."""
    try:
        proc = subprocess.run(
            ["git", "-C", base, *args],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            check=False,
        )
    except OSError:
        return None
    if proc.returncode != 0:
        return None
    out = (proc.stdout or "").strip()
    return out or None


def infer_github_from_checkout(base: str) -> tuple[str, str]:
    """Return ``(https_web_url, ref)`` inferred from a local git checkout.

    Reads ``remote.origin.url`` and the current branch.  If HEAD is
    detached, tries ``refs/remotes/origin/HEAD``, else falls back to
    ``main``.  Raises ``RuntimeError`` when origin cannot be resolved.
    """
    remote = _git(base, "remote", "get-url", "origin")
    if not remote:
        # Fallback: parse .git/config directly (works even without git on PATH
        # in odd environments, and when origin is unset in the worktree).
        cfg = os.path.join(base, ".git", "config")
        if os.path.isfile(cfg):
            section = None
            with open(cfg, "r", encoding="utf-8", errors="replace") as f:
                for line in f:
                    s = line.strip()
                    if s.startswith("[") and s.endswith("]"):
                        section = s[1:-1].strip()
                        continue
                    if section == 'remote "origin"' and s.startswith("url"):
                        _, _, val = s.partition("=")
                        remote = val.strip()
                        break
    if not remote:
        raise RuntimeError(
            f"cannot infer GitHub URL: no origin remote in {base!r} "
            f"(.git/config). Pass --base-url explicitly."
        )

    web = remote_url_to_https(remote)

    ref = _git(base, "rev-parse", "--abbrev-ref", "HEAD")
    if not ref or ref == "HEAD":
        # Detached HEAD — try origin/HEAD default branch.
        sym = _git(base, "symbolic-ref", "refs/remotes/origin/HEAD")
        if sym and sym.startswith("refs/remotes/origin/"):
            ref = sym[len("refs/remotes/origin/"):]
        else:
            # Read .git/HEAD as a last resort before falling back.
            head_path = os.path.join(base, ".git", "HEAD")
            if os.path.isfile(head_path):
                with open(head_path, "r", encoding="utf-8", errors="replace") as f:
                    head = f.read().strip()
                if head.startswith("ref: refs/heads/"):
                    ref = head[len("ref: refs/heads/"):]
                else:
                    ref = "main"
            else:
                ref = "main"
    return web, ref


def match_file_regex(file_re, abs_path: str, rel: str, name: str):
    """Return ``group(1)`` from the first successful ``file_re`` match.

    Tries, in order: relative POSIX path, basename (``match`` then
    ``search``), then file contents.  Returns ``None`` when nothing
    matches (caller should skip the file).
    """
    # Path with search so an unanchored pattern can hit a path suffix,
    # while ^...$ against a full path still works when intended.
    m = file_re.search(rel)
    if m:
        return m.group(1)
    # Basename with match so ^S_(.+)\.lean$ works as documented for FLT.
    m = file_re.match(name)
    if m:
        return m.group(1)
    m = file_re.search(name)
    if m:
        return m.group(1)
    try:
        with open(abs_path, "r", encoding="utf-8", errors="replace") as f:
            body = f.read()
    except OSError:
        return None
    m = file_re.search(body)
    if m:
        return m.group(1)
    return None


def list_files(base: str, source_subpath: str, file_prefix: str,
               recursive: bool, file_re=None
               ) -> tuple[list[tuple[str, str, str]], str]:
    """Return ``[(title, abs_path, rel_path_posix), ...]`` and the walked root.

    ``rel_path`` is always POSIX (forward slashes) so it can be appended
    to a GitHub base URL verbatim.  ``title`` is the theorem title / node
    ID used in emitted ``[title](url)`` lines.

    When ``file_re`` is a compiled regex, it is tried against the relative
    path, the basename, then the file contents (see
    :func:`match_file_regex`); ``group(1)`` becomes the title.  Otherwise
    ``file_prefix`` / module-name logic applies.
    """
    root = os.path.join(base, source_subpath) if source_subpath else base
    out: list[tuple[str, str, str]] = []

    def emit(abs_path: str) -> None:
        rel = os.path.relpath(abs_path, base).replace(os.sep, "/")
        name = os.path.basename(abs_path)
        if file_re is not None:
            title = match_file_regex(file_re, abs_path, rel, name)
            if title is None:
                return
        elif file_prefix:
            if not name.startswith(file_prefix):
                return
            title = name[len(file_prefix):-len(".lean")]
        else:
            # Module name: rel path without extension, / -> .
            title = rel[:-len(".lean")].replace("/", ".")
        out.append((title, abs_path, rel))

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
    ap.add_argument("--base", default=DEFAULT_BASE,
                    help="Local git checkout of the source Lean repo "
                         f"(default: {DEFAULT_BASE}). The GitHub URL for "
                         "[title](url) links is inferred from .git/config "
                         "(origin) unless --base-url is set. "
                         "A leading ~ is expanded.")
    ap.add_argument("--source-subpath", default="",
                    help="Subdir within --base containing source files "
                         "(e.g. 'P2M/Sol' for FLT, 'MathlibExt' for ATLAS).")
    ap.add_argument("--file-prefix", default="",
                    help="Filename prefix to strip when forming theorem "
                         "titles (e.g. 'S_' for FLT). Empty => use full "
                         "module name. Ignored when --file-regex is set.")
    ap.add_argument("--file-regex", default="",
                    help="Regex selecting theorems to port. Tried against "
                         "each file's relative POSIX path, basename, then "
                         "contents; group(1) is the theorem title used in "
                         "[title](url) output. Replaces --file-prefix. "
                         "Example (FLT): '^S_(.+)\\.lean$'.")
    ap.add_argument("--recursive", action="store_true",
                    help="Walk source subdir recursively (ATLAS / "
                         "--file-regex). Off => only top-level files "
                         "(legacy FLT --file-prefix on P2M/Sol).")
    ap.add_argument("--dep-filter", default="",
                    help="Regex applied to each import token; group(1) is "
                         "the dep ID. FLT uses '^Theorems\\.Thm_(\\w+)$'. "
                         "Empty => use the raw module path as dep ID.")
    ap.add_argument("--root", default="",
                    help="Node to pin last (FLT: 'fermat_last_theorem'). "
                         "Empty => no pinning (ATLAS).")
    ap.add_argument("--base-url", default="",
                    help="Override the GitHub URL used for [title](url) "
                         "docstring links. When omitted, inferred from "
                         "--base's .git/config (origin) + current branch. "
                         "Accepts a bare repo URL (expanded to "
                         ".../blob/<ref>) or an explicit .../blob/<ref> base.")
    ap.add_argument("--ported-root", default=DEFAULT_PORTED_ROOT,
                    help="Directory scanned for already-ported lemmas "
                         f"(default: {DEFAULT_PORTED_ROOT}). Pass empty "
                         "string to disable. A leading ~ is expanded.")
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
    args.base = os.path.expanduser(args.base)
    if args.ported_root:
        args.ported_root = os.path.expanduser(args.ported_root)

    t0 = time.time()

    file_re = None
    if args.file_regex:
        try:
            file_re = re.compile(args.file_regex)
        except re.error as e:
            print(f"ERROR: invalid --file-regex: {e}", file=sys.stderr)
            return 1
        if file_re.groups < 1:
            print("ERROR: --file-regex must contain a capturing group; "
                  "group(1) becomes the theorem title "
                  "(e.g. '^S_(.+)\\.lean$').", file=sys.stderr)
            return 1

    inferred_ref = "main"
    if args.base_url:
        # Explicit override wins; still normalise a bare repo URL.
        # Prefer the checkout's branch as the blob ref when the user
        # passed a bare URL without /blob/<ref>.
        try:
            _, inferred_ref = infer_github_from_checkout(args.base)
        except RuntimeError:
            inferred_ref = "main"
        base_url = normalize_base_url(args.base_url, default_ref=inferred_ref)
    else:
        try:
            web, inferred_ref = infer_github_from_checkout(args.base)
        except RuntimeError as e:
            print(f"ERROR: {e}", file=sys.stderr)
            return 1
        base_url = normalize_base_url(web, default_ref=inferred_ref)
    print(f"base-url: {base_url}  (ref={inferred_ref}"
          f"{', inferred' if not args.base_url else ', --base-url override'})",
          file=sys.stderr)

    files, _ = list_files(args.base, args.source_subpath,
                          args.file_prefix, args.recursive, file_re=file_re)
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

    body_lines = [f"[{k}]({base_url}/{path_of[k]})" for k in batch]
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
