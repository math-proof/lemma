"""
flt_port.py
============
Scaffold skeleton ``.lean`` files for the next batch of FLT theorems to port.

This is the next stage after :mod:`flt_topo_sort` has decided *which* FLT
theorems are ready.  Where that script only *lists* the next batch, this one
*creates* a working file for each unported theorem, with:

* the source-link docstring that ``flt_topo_sort.py``'s ``PORTED_RE`` regex
  already scans for (so the file is immediately recognised as ported, even
  though only the statement is filled in);
* the lemma statement copied verbatim from the FLT ``Theorems/Thm_<key>.lean``
  header (no need to re-derive it from ``P2M/Sol/S_<key>.lean``);
* a ``@[main] private lemma main`` placeholder with ``sorry`` as the proof
  body, so the porter only has to fill in the proof.

Path derivation
---------------
The mechanical default path is::

    Lemma/<word_1>/<word_2>/.../<word_n>.lean

i.e. the FLT key split on ``_`` becomes directory segments and the last word
becomes the filename (with the original casing preserved).  Example::

    AbsoluteValue_Completion_norm_coe_and_exists_one_lt_norm
        -> Lemma/AbsoluteValue/Completion/norm/coe/and/exists/one/lt/norm.lean

The porter may rename/move the file after the proof is in place.

Usage::

    # Default: use the topo-sort log next to this script.
    python py/flt_port.py

    # Dry-run (print what would happen, write nothing).
    python py/flt_port.py --dry-run

    # Limit the number of skeletons created.
    python py/flt_port.py --limit 5
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BASE = r"E:\github\lean\fermats-last-theorem"
DEFAULT_PORTED_ROOT = r"E:\github\lean\Lemma"
DEFAULT_BASE_URL = "https://github.com/anthropics/fermats-last-theorem/blob/main"
DEFAULT_LOG = Path(__file__).resolve().parent / "flt_topo_sort.log"
DEFAULT_DATE = "2026-09-20"

LINK_RE = re.compile(r"^\[([A-Za-z0-9_]+)\]\(https://[^)]+\)\s*$")
# Captures the text between `theorem <name>` and `:=`.  Handles the typical
# FLT formatting with `set_option ...` interspersed between name and sig.
THEOREM_RE = re.compile(
    r"^theorem\s+(?P<name>[A-Za-z0-9_.']+)\s*(?P<sig>.*?)\s*:=\s*",
    flags=re.DOTALL | re.MULTILINE,
)
# Strip the trailing `by p2m_exact_reverting ...` (used by FLT theorems to
# extract the statement from the corresponding solution's `theorem solution`).
P2M_EXACT_RE = re.compile(r"\s*:=\s*by\s+p2m_exact_reverting\b.*$", flags=re.DOTALL)
# Captures the proof body of `theorem solution` in P2M/Sol files.  The
# proof extends from after ``:=`` (or ``:= by``) to the next ``#print
# axioms`` line (or end of file).
SOLUTION_PROOF_RE = re.compile(
    r"theorem\s+solution\b[^\n]*?(?:\n[^\n]*?)*?\s*:=\s*(?:by\s*)?(?P<proof>.*?)(?=\n#print axioms|\Z)",
    flags=re.DOTALL,
)
# The line that introduces a theorem/statement begins with `theorem `.
THEOREM_LINE_RE = re.compile(r"^theorem\s+", flags=re.MULTILINE)


# ---------------------------------------------------------------------------
# Path derivation
# ---------------------------------------------------------------------------

def key_to_path(key: str, ported_root: Path) -> Path:
    """Mechanically derive a file path from an FLT key.

    Each ``_``-separated word becomes a directory segment (or, for the last
    word, the file name).  Original casing of each word is preserved.
    """
    words = key.split("_")
    return ported_root.joinpath(*words).with_suffix(".lean")


# ---------------------------------------------------------------------------
# FLT statement extraction
# ---------------------------------------------------------------------------

def extract_statement(theorems_dir: Path, key: str) -> tuple[str, str] | None:
    """Return the FLT theorem ``(name, signature)``.

    Reads ``Theorems/Thm_<key>.lean`` and returns the lemma name and its
    signature (the bit between ``theorem <name>`` and ``:=``).  The signature
    starts with whitespace (typically newline + indent) and runs until just
    before ``:=``.

    Returns ``None`` if the file is missing or the statement cannot be parsed.
    """
    path = theorems_dir / f"Thm_{key}.lean"
    if not path.exists():
        return None
    text = path.read_text(encoding="utf-8", errors="replace")
    m = THEOREM_RE.search(text)
    if not m:
        return None
    name = m.group("name")
    sig = m.group("sig")
    # Strip any trailing `:= by p2m_exact_reverting ...` tail just in case
    # the regex's lazy match left some bytes past the `:=`.
    sig = P2M_EXACT_RE.sub("", sig)
    return (name, sig.strip())


# ---------------------------------------------------------------------------
# Skeleton generation
# ---------------------------------------------------------------------------

def extract_proof(sol_dir: Path, key: str) -> str | None:
    """Return the proof body of ``P2M/Sol/S_<key>.lean``.

    Captures everything after ``:=`` (or ``:= by``) of the ``theorem
    solution`` declaration, up to the next ``#print axioms`` line (or end
    of file).  Returns ``None`` if the file is missing or the proof can't be
    located.

    Note: this is the FLT-side proof body verbatim — it still references
    ``solution`` and may use ``p2m_exact_reverting`` or other P2M.Util
    helpers.  The porter is expected to clean it up if ``lake build`` fails.
    """
    path = sol_dir / f"S_{key}.lean"
    if not path.exists():
        return None
    text = path.read_text(encoding="utf-8", errors="replace")
    m = SOLUTION_PROOF_RE.search(text)
    if not m:
        return None
    return m.group("proof").strip("\n")


def split_signature(sig: str) -> tuple[str, str]:
    """Split a theorem signature into ``(binders, conclusion)``.

    Looks for the rightmost ``:`` at paren/bracket depth 0 — the separator
    between binders and the conclusion in a Lean theorem signature.  Returns
    ``("", sig)`` if no such separator is found.
    """
    open_chars = set("([{⟨⟪")
    close_chars = set(")]}⟩⟫")
    depth = 0
    last_colon = -1
    for i, c in enumerate(sig):
        if c in open_chars:
            depth += 1
        elif c in close_chars:
            depth -= 1
        elif c == ":" and depth == 0:
            last_colon = i
    if last_colon == -1:
        return ("", sig)
    binders = sig[:last_colon].rstrip()
    conclusion = sig[last_colon + 1 :].lstrip()
    return (binders, conclusion)


def make_skeleton(
    key: str,
    base_url: str,
    statement: tuple[str, str] | None,
    proof: str | None = None,
    date: str = DEFAULT_DATE,
) -> str:
    """Build the contents of the skeleton ``.lean`` file.

    The source-link docstring matches the regex in
    ``flt_topo_sort.py:PORTED_RE`` so the file is detected as ported the
    moment it is created.

    The FLT statement is split into ``(binders, conclusion)`` at the top-level
    ``:``; the binders go under ``-- given`` and the conclusion under
    ``-- imply`` (matching the ``Lemma/*`` section layout convention).

    If ``proof`` is provided, it is substituted for the default ``sorry``
    body; otherwise the file is left as a stub.
    """
    src = f"[{key}]({base_url}/P2M/Sol/S_{key}.lean)"

    if statement is None:
        binders = ""
        conclusion = "True"
    else:
        _, sig = statement
        binders, conclusion = split_signature(sig)

    # Indent each binder line with two extra spaces so the body lines up
    # under the ``-- given`` header.
    binder_lines = binders.splitlines() if binders else []
    indented_binders = "\n  ".join(("  " + line if line else line) for line in binder_lines)
    if indented_binders:
        indented_binders += "\n  "
    else:
        indented_binders = ""

    proof_body = proof if proof else "sorry"
    # Indent each line of the proof body by two spaces so it nests under
    # ``-- proof``.
    indented_proof = "\n  ".join(("  " + line if line else line) for line in proof_body.splitlines())

    return f"""import Mathlib
import sympy.Basic


/--
{src}
-/
@[main]
private lemma main
-- given
  {indented_binders}:
-- imply
  {conclusion} := by
-- proof
  {indented_proof}


-- created on {date}
"""


# ---------------------------------------------------------------------------
# Topo log parsing & ported-set detection
# ---------------------------------------------------------------------------

def parse_log(path: Path) -> list[str]:
    """Extract FLT keys from a topo-sort log file (the ``[Key](URL)`` lines)."""
    keys: list[str] = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        m = LINK_RE.match(line)
        if m:
            keys.append(m.group(1))
    return keys


def ported_keys(ported_root: Path) -> set[str]:
    """Return the FLT keys whose source link appears in any ``.lean`` file."""
    PORTED_RE = re.compile(r"P2M/Sol/S_([A-Za-z0-9_]+)\.lean")
    keys: set[str] = set()
    if not ported_root.is_dir():
        return keys
    for dp, dns, fns in os.walk(ported_root):
        dns[:] = [d for d in dns if d not in (".lake", ".git")]
        for fn in fns:
            if not fn.endswith(".lean"):
                continue
            try:
                text = Path(dp, fn).read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            for m in PORTED_RE.finditer(text):
                keys.add(m.group(1))
    return keys


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(
        description=(
            "Scaffold skeleton .lean files for the next FLT port batch. "
            "Reads flt_topo_sort.log to discover the next batch, then for "
            "each unported key creates a mechanical-path skeleton."
        ),
    )
    ap.add_argument("--base", default=DEFAULT_BASE,
                    help="Root of the fermats-last-theorem project.")
    ap.add_argument("--ported-root", default=DEFAULT_PORTED_ROOT,
                    help="Directory to write skeleton files into.")
    ap.add_argument("--base-url", default=DEFAULT_BASE_URL,
                    help="GitHub base URL used in the source-link docstring.")
    ap.add_argument("--log", type=Path, default=DEFAULT_LOG,
                    help="Path of the topo-sort log to read.")
    ap.add_argument("--limit", type=int, default=20,
                    help="Maximum number of skeleton files to create.")
    ap.add_argument("--dry-run", action="store_true",
                    help="Print what would happen, write nothing.")
    ap.add_argument("--date", default=DEFAULT_DATE,
                    help="Date stamp inserted in `-- created on` footer.")
    args = ap.parse_args()

    base = Path(args.base)
    ported_root = Path(args.ported_root)
    theorems_dir = base / "Theorems"

    if not args.log.exists():
        print(f"ERROR: log file not found: {args.log}", file=sys.stderr)
        print("Run `python py/flt_topo_sort.py` first.", file=sys.stderr)
        return 1

    keys = parse_log(args.log)
    ported = ported_keys(ported_root)
    todo = [k for k in keys if k not in ported]

    print(f"topo log keys      : {len(keys)}")
    print(f"already ported     : {len(ported)}")
    print(f"to port (in batch) : {len(todo)}")
    print()

    created: list[tuple[str, Path]] = []
    skipped: list[tuple[str, Path]] = []
    missing_theorem: list[str] = []

    for key in todo:
        if len(created) >= args.limit:
            break
        path = key_to_path(key, ported_root)
        if path.exists():
            skipped.append((key, path))
            continue

        statement = extract_statement(theorems_dir, key)
        if statement is None:
            missing_theorem.append(key)

        proof = extract_proof(Path(args.base) / "P2M" / "Sol", key)

        if args.dry_run:
            created.append((key, path))
            continue

        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            make_skeleton(key, args.base_url, statement, proof, args.date),
            encoding="utf-8",
        )
        created.append((key, path))

    print(f"created {len(created)} skeleton file(s):")
    for key, path in created:
        rel = path.relative_to(ROOT) if path.is_absolute() else path
        print(f"  {key} -> {rel}")

    if skipped:
        print()
        print(f"skipped {len(skipped)} (already exist):")
        for key, path in skipped[:5]:
            rel = path.relative_to(ROOT) if path.is_absolute() else path
            print(f"  {key} -> {rel}")
        if len(skipped) > 5:
            print(f"  ... and {len(skipped) - 5} more")

    if missing_theorem:
        print()
        print(f"warning: {len(missing_theorem)} key(s) had no Thm_<key>.lean:")
        for key in missing_theorem[:5]:
            print(f"  {key}")
        if len(missing_theorem) > 5:
            print(f"  ... and {len(missing_theorem) - 5} more")

    print()
    print("Next step: read each FLT solution at")
    print(f"  {base}\\P2M\\Sol\\S_<key>.lean")
    print("and replace the `sorry` with the actual proof.  When done, re-run")
    print("`python py/flt_topo_sort.py` to advance the queue.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())