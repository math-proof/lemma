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

Path derivation (two phases)
----------------------------
Lemma naming is intentionally two-phase:

1. **Rough** (lean.js) — ``node mjs/suggestLemmaPath.mjs`` parses the
   skeleton source with lean.js and proposes a provisional ``Lemma/…`` path
   *before* a finished proof.  Used when scaffolding.
2. **Precise** (``Name.toJson`` / ``imply.struct``) — ``node
   mjs/suggestFromLean.mjs`` enumerates elaborator-faithful alts after the
   statement typechecks (proof may still be ``sorry``).  Used by
   ``--finalize``.

Fallback for phase 1 if lean.js suggest fails: mechanical key split::

    AbsoluteValue_Completion_norm_coe_and_exists_one_lt_norm
        -> Lemma/AbsoluteValue/Completion/norm/coe/and/exists/one/lt/norm.lean

Usage::

    # Scaffold the next *one* ready theorem (default --limit 1).
    python py/flt_port.py

    # Dry-run.
    python py/flt_port.py --dry-run

    # Later, when single-lemma flow is solid: batch N independent keys.
    python py/flt_port.py --limit 5

    # Phase 1 only (same as default scaffold; explicit).
    python py/flt_port.py --rough-only

    # Phase 2: check / suggest precise paths for existing files.
    python py/flt_port.py --finalize Lemma/Foo/Bar.lean

    # Phase 2 + actually move when inconsistent.
    python py/flt_port.py --finalize --apply-rename Lemma/Foo/Bar.lean
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BASE = r"E:\github\lean\fermats-last-theorem"
DEFAULT_PORTED_ROOT = r"E:\github\lean\Lemma"
DEFAULT_BASE_URL = "https://github.com/anthropics/fermats-last-theorem/blob/main"
DEFAULT_LOG = Path(__file__).resolve().parent / "flt_topo_sort.log"
DEFAULT_DATE = "2026-09-20"

# Phase-1 / phase-2 suggesters (orchestration only; naming lives in mjs/).
SUGGEST_ROUGH = ROOT / "mjs" / "suggestLemmaPath.mjs"
SUGGEST_PRECISE = ROOT / "mjs" / "suggestFromLean.mjs"

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


def _run_node_json(script: Path, *args: str) -> dict:
    """Run ``node <script> --json …`` and parse stdout as JSON."""
    cmd = ["node", str(script), "--json", *args]
    proc = subprocess.run(
        cmd,
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        err = (proc.stderr or proc.stdout or "").strip()
        raise RuntimeError(err or f"node exited {proc.returncode}")
    return json.loads(proc.stdout)



# Structural path segments allowed at length 1–2 (lemma naming connectives).
_ROUGH_STRUCT = {
    "eq", "ne", "is", "as", "of", "ae", "et", "ou", "lt", "gt", "le", "ge",
    "in", "to", "dvd", "sub", "sup", "ll", "gg",
}


def _rough_path_sane(rel: str) -> bool:
    """Reject lean.js rough paths that are clearly junk for scaffolding.

    FLT Mathlib statements often emit Greek binder glyphs or 1-char atoms;
    those should fall back to the mechanical key path.
    """
    parts = [x for x in rel.replace("\\", "/").split("/") if x]
    if not parts or not parts[-1].endswith(".lean"):
        return False
    segs = parts[:-1] + [parts[-1][: -len(".lean")]]
    for seg in segs:
        if not seg:
            return False
        if any(ord(c) > 127 for c in seg):
            return False
        soft = seg.lower()
        if soft in _ROUGH_STRUCT:
            continue
        # Content atoms should be CamelCase-ish and longer than 1 char.
        if len(seg) < 2:
            return False
    return True


def rough_path_from_source(source: str, ported_root: Path) -> Path | None:
    """Phase 1: lean.js rough path from skeleton source text.

    Writes ``source`` to a temp ``.lean`` file, runs
    ``mjs/suggestLemmaPath.mjs --json``, and maps ``suggestedPath`` under
    ``ported_root``.  Returns ``None`` on any failure (caller falls back to
    :func:`key_to_path`).
    """
    if not SUGGEST_ROUGH.is_file():
        return None
    tmp: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            suffix=".lean",
            delete=False,
            encoding="utf-8",
        ) as fh:
            fh.write(source)
            tmp = Path(fh.name)
        data = _run_node_json(SUGGEST_ROUGH, str(tmp))
        rel = str(data.get("suggestedPath") or "").replace(chr(92), "/").lstrip("/")
        if rel.startswith("Lemma/"):
            rel = rel[len("Lemma/") :]
        if not rel.endswith(".lean"):
            return None
        if not _rough_path_sane(rel):
            print(f"  (rough suggest rejected: {rel})", file=sys.stderr)
            return None
        return ported_root.joinpath(*rel.split("/"))
    except Exception as exc:  # noqa: BLE001 — fallback is intentional
        print(f"  (rough suggest failed: {exc})", file=sys.stderr)
        return None
    finally:
        if tmp is not None:
            try:
                tmp.unlink()
            except OSError:
                pass


def precise_suggest(lean_file: Path) -> dict:
    """Phase 2: elaborator-precise alts via ``mjs/suggestFromLean.mjs --json``."""
    return _run_node_json(SUGGEST_PRECISE, str(lean_file))


def best_precise_target(result: dict, ported_root: Path) -> str | None:
    """Pick rename target: matched path if consistent, else shortest free alt."""
    if result.get("consistent") and result.get("matchedSuggestion"):
        return result["matchedSuggestion"]
    for alt in result.get("suggestions") or []:
        abs_path = ported_root / Path(alt)
        if not abs_path.exists():
            return alt
    all_alts = result.get("allSuggestions") or []
    return all_alts[0] if all_alts else None


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
            "Scaffold FLT port skeletons (phase-1 lean.js rough path) and/or "
            "finalize paths with phase-2 Name.toJson suggestFromLean."
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
    ap.add_argument("--limit", type=int, default=1,
                    help="Max skeletons to create (default 1; raise later for batch).")
    ap.add_argument("--dry-run", action="store_true",
                    help="Print what would happen, write nothing.")
    ap.add_argument("--date", default=DEFAULT_DATE,
                    help="Date stamp inserted in `-- created on` footer.")
    ap.add_argument(
        "--rough-only",
        action="store_true",
        help="Scaffold only (phase 1). Same as default create flow.",
    )
    ap.add_argument(
        "--finalize",
        action="store_true",
        help="Phase 2: run suggestFromLean on existing .lean paths.",
    )
    ap.add_argument(
        "--apply-rename",
        action="store_true",
        help="With --finalize, move file to best precise path when inconsistent.",
    )
    ap.add_argument(
        "paths",
        nargs="*",
        help="With --finalize: Lemma/.../.lean files (or absolute paths) to check.",
    )
    args = ap.parse_args()

    ported_root = Path(args.ported_root)

    if args.finalize:
        return _cmd_finalize(args, ported_root)

    # Default / --rough-only: scaffold next batch with phase-1 paths.
    return _cmd_scaffold(args, ported_root)


def _cmd_scaffold(args: argparse.Namespace, ported_root: Path) -> int:
    base = Path(args.base)
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
    print(f"phase-1 rough      : {SUGGEST_ROUGH.name}")
    print()

    if not todo:
        print("log batch exhausted (all listed keys already ported).")
        print("Re-run: python py/flt_topo_sort.py")
        print("Then:   python py/flt_port.py")
        return 0

    created: list[tuple[str, Path, str]] = []
    skipped: list[tuple[str, Path]] = []
    missing_theorem: list[str] = []

    for key in todo:
        if len(created) >= args.limit:
            break

        statement = extract_statement(theorems_dir, key)
        if statement is None:
            missing_theorem.append(key)

        proof = extract_proof(Path(args.base) / "P2M" / "Sol", key)
        text = make_skeleton(key, args.base_url, statement, proof, args.date)

        fallback = key_to_path(key, ported_root)
        rough = rough_path_from_source(text, ported_root)
        path = rough if rough is not None else fallback
        how = "rough" if rough is not None else "key"

        if path.exists():
            skipped.append((key, path))
            continue

        if args.dry_run:
            created.append((key, path, how))
            continue

        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        created.append((key, path, how))

    print(f"created {len(created)} skeleton file(s):")
    for key, path, how in created:
        try:
            rel = path.relative_to(ROOT)
        except ValueError:
            rel = path
        print(f"  [{how}] {key} -> {rel}")

    if skipped:
        print(f"\nskipped {len(skipped)} (already on disk):")
        for key, path in skipped:
            try:
                rel = path.relative_to(ROOT)
            except ValueError:
                rel = path
            print(f"  {key} -> {rel}")

    if missing_theorem:
        print(f"\nWARNING: no Theorems/Thm_*.lean for {len(missing_theorem)} key(s):")
        for key in missing_theorem:
            print(f"  {key}")

    if args.rough_only:
        print("\n(--rough-only: scaffold done; run --finalize later for phase 2)")

    return 0


def _cmd_finalize(args: argparse.Namespace, ported_root: Path) -> int:
    if not SUGGEST_PRECISE.is_file():
        print(f"ERROR: missing {SUGGEST_PRECISE}", file=sys.stderr)
        return 1
    if not args.paths:
        print(
            "ERROR: --finalize needs one or more Lemma/.../.lean paths",
            file=sys.stderr,
        )
        return 1

    print(f"phase-2 precise : {SUGGEST_PRECISE.name}")
    print(f"apply rename    : {args.apply_rename}")
    print()

    rc = 0
    for raw in args.paths:
        lean = Path(raw)
        if not lean.is_absolute():
            cand = ROOT / lean
            lean = cand if cand.exists() else Path(raw)
        if not lean.exists():
            print(f"MISSING {raw}")
            rc = 1
            continue
        try:
            result = precise_suggest(lean)
        except Exception as exc:  # noqa: BLE001
            print(f"FAIL {lean}: {exc}")
            rc = 1
            continue

        cur = result.get("currentPath") or ""
        ok = bool(result.get("consistent"))
        target = best_precise_target(result, ported_root)
        status = "consistent" if ok else "inconsistent"
        print(f"{status}: Lemma/{cur}")
        if target and not ok:
            print(f"  suggest: Lemma/{target}")
            dest = ported_root / Path(target)
            if args.apply_rename and not args.dry_run:
                if dest.exists():
                    print(f"  SKIP rename (exists): {dest}")
                else:
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    lean.rename(dest)
                    print(f"  renamed -> Lemma/{target}")
            elif args.apply_rename and args.dry_run:
                print(f"  dry-run rename -> Lemma/{target}")
        elif ok:
            print("  (exact match among alts)")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
