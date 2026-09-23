"""
theorem_port.py
===============
Scaffold skeleton ``.lean`` files for porting theorems from **any source**
(mathlib PRs, FLT, rl-theory-in-lean, external repos, scratch files) into
this repo's ``Lemma/`` tree.

The script reads a source ``.lean`` file, applies the **PORTING RULES**
(below) to transform it into the repo's flat ``@[main] private lemma main``
format, derives a ``Lemma/…`` path via the two-phase suggester, and writes
the skeleton with ``sorry`` (or the source proof, if extractable).

PORTING RULES (prompt engineering)
----------------------------------
When transforming source Lean into the repo skeleton format, apply these
rules in order:

1. **Remove ``namespace`` statements.**
   Delete every ``namespace X`` and its matching ``end X`` (or bare
   ``end``).  Dedent the enclosed declarations by one level (2 spaces).
   Rationale: the repo uses top-level ``@[main] private lemma main`` so
   that ``Name.lemmaName`` produces the correct chapter-level name
   (e.g. ``Real.Maclaurin``).  A ``@[main] private lemma main`` inside
   ``namespace Multiset`` has ``declName = Multiset.main`` whose
   ``suffix`` decapitalizes *all* components, yielding garbage names.

2. **Remove ``variable`` statements.**
   Delete every ``variable`` line.  The repo has ``autoImplicit`` enabled,
   so type variables (``α``, ``β``, …) and value variables (``a``, ``b``,
   …) are bound automatically from their occurrences in the theorem
   signature.  Explicit ``variable`` lines would shadow or conflict with
   autoImplicit binders.
   Caveat: if the source ``variable`` carried hypotheses (e.g.
   ``variable (h : Continuous f)``), those hypotheses must be added
   explicitly to the lemma's binder list.  Review the transformed output.

3. **Convert ``theorem`` to ``private lemma``.**
   Replace every ``theorem X`` with ``private lemma X``.  Only the main
   result should be public; all helpers are ``private``.  (The main
   result itself is also ``private lemma main`` — see rule 4 — but it is
   exported via ``@[main]`` to a public chapter-level name.)

4. **Exactly one ``@[main] private lemma main``.**
   Among all declarations in the file, exactly one — the ported theorem —
   must be named ``main``, declared ``private lemma main``, and
   attributed ``@[main]``.  All other declarations are ``private lemma``
   (helpers) without ``@[main]``.
   ``@[main]`` must be at **top level** (outside any namespace) so that
   ``Name.lemmaName`` generates ``<Chapter>.<TheoremName>`` rather than
   names with namespace suffixes (see rule 1).

5. **``def`` before ``lemma``.**
   Place all ``def`` (and ``noncomputable def``) declarations before any
   ``lemma`` declarations.  This keeps definitions visible to all lemmas
   that reference them without forward-declaration issues, and matches
   the repo's top-to-bottom readability convention.

Rules 1–3 and 5 are applied mechanically by :func:`transform_source`.
Rule 4 is applied by :func:`make_skeleton` which wraps the main theorem
in ``@[main] private lemma main``.  Edge cases (multi-line attributes,
hypothesis-carrying ``variable``, nested namespaces) may require manual
cleanup after scaffolding.

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

Usage
-----
::

    # Scaffold from a single source file.
    python py/theorem_port.py path/to/Source.lean

    # With explicit source URL for the docstring link.
    python py/theorem_port.py path/to/Source.lean \\
        --source-url https://github.com/foo/bar/blob/main/Source.lean

    # Specify which theorem to port (default: last theorem in file).
    python py/theorem_port.py path/to/Source.lean --theorem-name main_thm

    # Dry-run.
    python py/theorem_port.py path/to/Source.lean --dry-run

    # Skip mechanical transformation (use source as-is).
    python py/theorem_port.py path/to/Source.lean --no-transform

    # Phase 2: check / suggest precise paths for existing files.
    python py/theorem_port.py --finalize Lemma/Foo/Bar.lean

    # Phase 2 + actually move when inconsistent.
    python py/theorem_port.py --finalize --apply-rename Lemma/Foo/Bar.lean
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PORTED_ROOT = ROOT / "Lemma"
DEFAULT_DATE = date.today().isoformat()

# Phase-1 / phase-2 suggesters (orchestration only; naming lives in mjs/).
SUGGEST_ROUGH = ROOT / "mjs" / "suggestLemmaPath.mjs"
SUGGEST_PRECISE = ROOT / "mjs" / "suggestFromLean.mjs"

# --- Regex patterns ---------------------------------------------------------

# Declaration start: optional attributes, optional modifiers, kind, name.
DECL_START_RE = re.compile(
    r'^(?:@\[[^\]]+\]\s*)*'
    r'(?:noncomputable\s+|private\s+|protected\s+)*'
    r'(def|theorem|lemma)\s+'
    r"([A-Za-z0-9_.']+)",
)
# Theorem/lemma with full signature up to := (handles private/protected).
THEOREM_SIG_RE = re.compile(
    r'^(?:private\s+|protected\s+)?(?P<kind>theorem|lemma)\s+'
    r"(?P<name>[A-Za-z0-9_.']+)\s*(?P<sig>.*?)\s*:=\s*",
    re.DOTALL | re.MULTILINE,
)
NAMESPACE_START_RE = re.compile(r'^\s*namespace\b')
END_RE = re.compile(r'^\s*end\b')
VARIABLE_RE = re.compile(r'^\s*variable\b')
THEOREM_TO_LEMMA_RE = re.compile(r'^(\s*)theorem\b')


# ---------------------------------------------------------------------------
# Path derivation
# ---------------------------------------------------------------------------

def key_to_path(key: str, ported_root: Path) -> Path:
    """Mechanically derive a file path from a ``_``-separated key.

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

    Mathlib statements often emit Greek binder glyphs or 1-char atoms;
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
# Source transformation (PORTING RULES 1, 2, 3, 5)
# ---------------------------------------------------------------------------

def transform_source(text: str) -> str:
    """Apply porting rules 1, 2, 3, 5 to source Lean text.

    Rule 1: Remove ``namespace``/``end`` and dedent enclosed code.
    Rule 2: Remove ``variable`` lines.
    Rule 3: Convert ``theorem`` → ``private lemma``.
    Rule 5: Reorder so all ``def`` declarations precede ``lemma`` declarations.

    Rule 4 (``@[main] private lemma main``) is handled by
    :func:`make_skeleton`, not here.

    Returns the transformed text.  Edge cases (hypothesis-carrying
    ``variable``, nested namespaces, multi-line attributes) may need
    manual review — see the PORTING RULES in the module docstring.
    """
    lines = text.splitlines()

    # --- Rule 1: Remove namespace/end and dedent ---
    transformed: list[str] = []
    dedent = 0
    for line in lines:
        stripped = line.lstrip()
        if NAMESPACE_START_RE.match(line):
            dedent += 1
            continue
        if END_RE.match(line) and dedent > 0:
            dedent -= 1
            continue
        if dedent > 0:
            indent = len(line) - len(stripped)
            new_indent = max(0, indent - 2 * dedent)
            line = " " * new_indent + stripped
        transformed.append(line)

    # --- Rule 2: Remove variable lines ---
    transformed = [l for l in transformed if not VARIABLE_RE.match(l)]

    # --- Rule 3: Convert theorem → private lemma ---
    transformed = [
        THEOREM_TO_LEMMA_RE.sub(r"\1private lemma ", l, count=1)
        for l in transformed
    ]

    text = "\n".join(transformed)

    # --- Rule 5: Move def before lemma ---
    text = _reorder_def_before_lemma(text)

    return text


def _reorder_def_before_lemma(text: str) -> str:
    """Move all ``def`` blocks before ``lemma``/``theorem`` blocks.

    Splits text into top-level blocks separated by blank lines, classifies
    each as ``def``, ``lemma``, or ``other`` (imports, comments, etc.),
    and re-emits them as: ``other`` (preserving original order) → ``def``
    → ``lemma``.
    """
    blocks = re.split(r"\n{2,}", text)
    others: list[str] = []
    defs: list[str] = []
    lemmas: list[str] = []
    for block in blocks:
        stripped = block.lstrip()
        if re.match(r"^(?:noncomputable\s+)?def\b", stripped):
            defs.append(block)
        elif re.match(r"^(?:private\s+|protected\s+)?(?:lemma|theorem)\b", stripped):
            lemmas.append(block)
        else:
            others.append(block)
    return "\n\n".join(others + defs + lemmas)


# ---------------------------------------------------------------------------
# Source extraction (generalized — works on any Lean file)
# ---------------------------------------------------------------------------

def find_declarations(text: str) -> list[tuple[int, str, str]]:
    """Find declaration starts in text.

    Returns a list of ``(line_index, kind, name)`` where ``kind`` is
    ``def``/``theorem``/``lemma`` and ``name`` is the declaration name.
    Handles optional attributes (``@[main]``) and modifiers
    (``private``/``protected``/``noncomputable``).
    """
    decls: list[tuple[int, str, str]] = []
    for i, line in enumerate(text.splitlines()):
        m = DECL_START_RE.match(line)
        if m:
            decls.append((i, m.group(1), m.group(2)))
    return decls


def extract_statement_from_text(
    text: str, theorem_name: str | None = None,
) -> tuple[str, str] | None:
    """Extract ``(name, signature)`` from source Lean text.

    If ``theorem_name`` is given, find that specific theorem/lemma.
    Otherwise, return the last theorem/lemma in the file (convention:
    the main result comes after helpers).
    """
    decls = find_declarations(text)
    lemmas = [(i, k, n) for i, k, n in decls if k in ("theorem", "lemma")]
    if not lemmas:
        return None
    if theorem_name is not None:
        matches = [d for d in lemmas if d[2] == theorem_name]
        if not matches:
            return None
        target = matches[0]
    else:
        target = lemmas[-1]  # last lemma = main theorem (convention)

    lines = text.splitlines()
    start = target[0]
    buf: list[str] = []
    for i in range(start, len(lines)):
        buf.append(lines[i])
        joined = "\n".join(buf)
        m = THEOREM_SIG_RE.search(joined)
        if m:
            return (m.group("name"), m.group("sig").strip())
    return None


def extract_proof_from_text(
    text: str, theorem_name: str | None = None,
) -> str | None:
    """Extract the proof body of a theorem/lemma from source Lean text.

    Returns the text after ``:=`` (or ``:= by``) up to the next declaration
    or end of file.  If ``theorem_name`` is given, find that specific
    declaration; otherwise use the last theorem/lemma.
    """
    decls = find_declarations(text)
    lemmas = [(i, k, n) for i, k, n in decls if k in ("theorem", "lemma")]
    if not lemmas:
        return None
    if theorem_name is not None:
        matches = [d for d in lemmas if d[2] == theorem_name]
        if not matches:
            return None
        target = matches[0]
    else:
        target = lemmas[-1]

    # Find the next declaration after the target.
    next_start = len(text.splitlines())
    for i, _, _ in decls:
        if i > target[0]:
            next_start = i
            break

    lines = text.splitlines()
    # Find the := line
    proof_start: int | None = None
    for i in range(target[0], next_start):
        if ":=" in lines[i]:
            proof_start = i
            break
    if proof_start is None:
        return None

    # Extract proof: everything after := on the same line, plus subsequent lines.
    after_eq = lines[proof_start].split(":=", 1)[1]
    proof_lines = [after_eq.strip()]
    proof_lines.extend(lines[proof_start + 1 : next_start])
    proof = "\n".join(proof_lines).strip()
    # Strip leading "by" if present (the skeleton adds ":= by").
    proof = re.sub(r"^by\s+", "", proof)
    return proof if proof else None


def extract_defs_and_helpers(
    text: str, main_name: str,
) -> tuple[str, str]:
    """Extract ``def`` blocks and helper lemma blocks from transformed text.

    Returns ``(defs_text, helpers_text)`` where ``defs_text`` is all
    ``def``/``noncomputable def`` blocks and ``helpers_text`` is all
    ``private lemma`` blocks whose name is not ``main_name``.
    Both are returned as plain text (already transformed by
    :func:`transform_source`).
    """
    decls = find_declarations(text)
    lines = text.splitlines()
    blocks: list[tuple[str, str, str]] = []
    for idx, (start, kind, name) in enumerate(decls):
        end = decls[idx + 1][0] if idx + 1 < len(decls) else len(lines)
        block = "\n".join(lines[start:end]).strip()
        blocks.append((kind, name, block))
    defs = [b for k, n, b in blocks if k == "def"]
    helpers = [
        b for k, n, b in blocks
        if k in ("lemma", "theorem") and n != main_name
    ]
    return (
        "\n\n".join(defs) if defs else "",
        "\n\n".join(helpers) if helpers else "",
    )


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


# ---------------------------------------------------------------------------
# Skeleton generation (PORTING RULE 4)
# ---------------------------------------------------------------------------

def make_skeleton(
    source_url: str | None,
    statement: tuple[str, str] | None,
    proof: str | None = None,
    defs: str = "",
    helpers: str = "",
    date: str = DEFAULT_DATE,
) -> str:
    """Build the contents of the skeleton ``.lean`` file.

    Applies PORTING RULE 4: the main theorem is wrapped as
    ``@[main] private lemma main`` with ``-- given`` / ``-- imply`` /
    ``-- proof`` section comments.  Helper ``def`` and ``lemma``
    declarations (already transformed by :func:`transform_source`) are
    placed before the main lemma (rule 5).
    """
    if statement is None:
        binders = ""
        conclusion = "True"
    else:
        _, sig = statement
        binders, conclusion = split_signature(sig)

    # Indent each binder line with two extra spaces so the body lines up
    # under the ``-- given`` header.
    binder_lines = binders.splitlines() if binders else []
    indented_binders = "\n  ".join(
        ("  " + line if line else line) for line in binder_lines
    )
    if indented_binders:
        indented_binders += "\n  "
    else:
        indented_binders = ""

    proof_body = proof if proof else "sorry"
    # Indent each line of the proof body by two spaces so it nests under
    # ``-- proof``.
    indented_proof = "\n  ".join(
        ("  " + line if line else line) for line in proof_body.splitlines()
    )

    # Source link docstring
    if source_url:
        docstring = f"/--\n{source_url}\n-/"
    else:
        docstring = "/-- ported from external source -/"

    # Build preamble: docstring → defs → helpers (rule 5: def before lemma).
    preamble_parts = [docstring]
    if defs:
        preamble_parts.append(defs)
    if helpers:
        preamble_parts.append(helpers)
    preamble = "\n\n".join(preamble_parts)

    return f"""import Mathlib
import sympy.Basic


{preamble}

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
# Driver
# ---------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(
        description=(
            "Scaffold port skeletons from any source Lean file "
            "(phase-1 lean.js rough path) and/or finalize paths with "
            "phase-2 Name.toJson suggestFromLean."
        ),
    )
    ap.add_argument(
        "source", nargs="?", default=None,
        help="Source .lean file containing the theorem to port.",
    )
    ap.add_argument("--source-url", default=None,
                    help="Source URL for the docstring link.")
    ap.add_argument("--theorem-name", default=None,
                    help="Name of the theorem to port (default: last in file).")
    ap.add_argument("--ported-root", default=DEFAULT_PORTED_ROOT,
                    help="Directory to write skeleton files into.")
    ap.add_argument("--dry-run", action="store_true",
                    help="Print what would happen, write nothing.")
    ap.add_argument("--date", default=DEFAULT_DATE,
                    help="Date stamp inserted in `-- created on` footer.")
    ap.add_argument("--no-transform", action="store_true",
                    help="Skip mechanical transformation (use source as-is).")
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

    if args.source is None:
        ap.error("SOURCE.lean is required (or use --finalize with paths).")

    return _cmd_scaffold(args, ported_root)


def _cmd_scaffold(args: argparse.Namespace, ported_root: Path) -> int:
    source = Path(args.source)
    if not source.is_absolute():
        source = ROOT / source
    if not source.exists():
        print(f"ERROR: source file not found: {source}", file=sys.stderr)
        return 1

    text = source.read_text(encoding="utf-8", errors="replace")

    # Apply porting rules (1, 2, 3, 5) unless --no-transform.
    if not args.no_transform:
        text = transform_source(text)

    # Extract the main statement and proof.
    statement = extract_statement_from_text(text, args.theorem_name)
    if statement is None:
        print(f"ERROR: no theorem/lemma found in {source}", file=sys.stderr)
        return 1
    main_name = statement[0]
    proof = extract_proof_from_text(text, args.theorem_name)

    # Extract defs and helpers (rule 5: before main lemma).
    defs, helpers = extract_defs_and_helpers(text, main_name)

    # Build the skeleton (rule 4: @[main] private lemma main).
    skeleton = make_skeleton(
        args.source_url, statement, proof, defs, helpers, args.date,
    )

    # Derive path (phase 1 rough).
    fallback = key_to_path(main_name, ported_root)
    rough = rough_path_from_source(skeleton, ported_root)
    path = rough if rough is not None else fallback
    how = "rough" if rough is not None else "key"

    if path.exists():
        print(f"SKIP (already exists): {path}")
        return 0

    print(f"theorem   : {main_name}")
    print(f"phase-1   : {how}")
    print(f"proof     : {'extracted' if proof else 'sorry'}")
    print(f"defs      : {bool(defs)}")
    print(f"helpers   : {bool(helpers)}")

    if args.dry_run:
        print(f"\n(dry-run) would write to: {path}")
        return 0

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(skeleton, encoding="utf-8")
    try:
        rel = path.relative_to(ROOT)
    except ValueError:
        rel = path
    print(f"\ncreated: {rel}")
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