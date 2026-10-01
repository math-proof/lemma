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

6. **Source docstring is a ``[label](url)`` link.**
   The docstring before the ported lemma must be exactly
   ``/--\n[<theorem_name>](https://github.com/anthropics/fermats-last-theorem/blob/main/...)\n-/`` — a markdown link whose label
   names the source theorem (for FLT, the file stem without ``S_``; for
   Mathlib/RL, the project name) — never a bare URL.  It is the clue that this theorem is already proven elsewhere,
   so tooling and readers can find the original proof.  Applied by
   :func:`make_skeleton` via :func:`source_link`.

7. **Signature layout (see AGENTS.md).**  Strictly 2-indented.  Before
   ``-- given``, in order: (a) one line of standalone instances
   ``[NormedAddCommGroup E] [NormedSpace ℝ E]``; (b) one line per implicit
   binder with its dependent instances, e.g. ``{p : Prop} [Decidable p]``;
   (c) one line per bare implicit binder ``{d : ℕ}``.  Bare ``{E : Type*}``
   binders are dropped (autoImplicit binds ``E`` from the instances).  After ``-- given``:
   the explicit binders in source order, ending with
   `` :`` on the same line, e.g. ``(χ : AddChar E Circle) (hχ : Continuous χ) :``.
   Never put ``{..}``/``[..]`` binders under ``-- given`` and never put the
   ``:`` on its own line.  The proof body is also 2-indented.  Applied by
   :func:`layout_binders`.

Rules 1–3 and 5 are applied mechanically by :func:`transform_source`.
Rules 4, 6 and 7 are applied by :func:`make_skeleton` which wraps the main theorem
in ``@[main] private lemma main``.  Edge cases (multi-line attributes,
hypothesis-carrying ``variable``, nested namespaces) may require manual
cleanup after scaffolding.

Path derivation (two phases)
----------------------------
Lemma naming is intentionally two-phase; both call ``mjs/lemmaPath.mjs``:

1. **Rough** — ``node mjs/lemmaPath.mjs --json`` on a temp file of the
   skeleton source proposes a provisional ``Lemma/…`` path *before* a
   finished proof.  Used when scaffolding (falls back to :func:`key_to_path`
   on failure).
2. **Finalize** — ``node mjs/lemmaPath.mjs --json`` re-checks an existing
   ``Lemma/…`` path against the statement AST.  Used by ``--finalize``.

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
import textwrap
import subprocess
import sys
import tempfile
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PORTED_ROOT = ROOT / "Lemma"
DEFAULT_DATE = date.today().isoformat()

# Path suggester for phase 1 (scaffold) and phase 2 (finalize); naming lives in mjs/.
SUGGEST_LEMMAPATH = ROOT / "mjs" / "lemmaPath.mjs"

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
SECTION_START_RE = re.compile(r'^\s*section\b')
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


def flt_key_from_source(source: Path) -> str | None:
    """Return the FLT theorem key encoded in an ``S_<key>.lean`` /
    ``Thm_<key>.lean`` file name, or ``None`` for other sources."""
    for prefix in ("S_", "Thm_"):
        if source.stem.startswith(prefix):
            return source.stem[len(prefix):]
    return None


def fallback_path_for(
    source: Path, main_name: str, ported_root: Path,
) -> Path:
    """Phase-1 fallback when the rough path suggester fails.

    For FLT sources the main theorem is almost always named ``solution``,
    so deriving a path from the theorem name collapses every file onto
    ``Lemma/solution.lean``; derive the path from the ``S_<key>`` file
    name instead, reusing ``flt_topo_sort.key_to_path``.  Other sources
    fall back to the theorem-name key path.
    """
    flt_key = flt_key_from_source(source)
    if flt_key is not None:
        try:
            sys.path.insert(0, str(Path(__file__).resolve().parent))
            from flt_topo_sort import key_to_path as flt_key_to_path

            segments = flt_key_to_path(flt_key)
            return ported_root.joinpath(*segments).with_suffix(".lean")
        except Exception:  # noqa: BLE001 — generic fallback must still work
            pass
    return key_to_path(main_name, ported_root)


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
    ``mjs/lemmaPath.mjs --json``, and maps ``suggestedPath`` under
    ``ported_root``.  Returns ``None`` on any failure (caller falls back to
    :func:`key_to_path`).
    """
    if not SUGGEST_LEMMAPATH.is_file():
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
        data = _run_node_json(SUGGEST_LEMMAPATH, str(tmp))
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
    """Phase 2: path check via ``mjs/lemmaPath.mjs --json``."""
    return _run_node_json(SUGGEST_LEMMAPATH, str(lean_file))


def _consistent_ok(result: dict) -> bool:
    c = result.get("consistent")
    if isinstance(c, dict):
        return bool(c.get("ok"))
    return bool(c)


def best_precise_target(result: dict, ported_root: Path) -> str | None:
    """Pick rename target: current path if consistent, else suggestedPath / free alt."""
    if _consistent_ok(result):
        return result.get("currentPath")
    candidates = []
    sp = result.get("suggestedPath")
    if sp:
        candidates.append(sp)
    candidates.extend(result.get("suggestions") or [])
    for alt in candidates:
        abs_path = ported_root / Path(alt)
        if not abs_path.exists():
            return alt
    return candidates[0] if candidates else None


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
        if NAMESPACE_START_RE.match(line) or SECTION_START_RE.match(line):
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


def _decl_chunks(text: str) -> list[tuple[str | None, str]]:
    """Split text into top-level ``(kind, chunk)`` pieces.

    A declaration piece spans from its ``def``/``lemma``/``theorem`` start
    line to the line just before the next top-level declaration — blank
    lines and the entire (possibly multi-paragraph) proof stay attached.
    ``kind`` is ``None`` for anything else (imports, options, comments,
    ``structure``, section markers, …).  Column-0 ``@[…]`` attribute lines
    (including multi-line attribute blocks) are attached to the declaration
    they precede.

    Splitting on blank lines, as an earlier version did, severed a proof
    written as ``:= by\\n\\n  <proof>`` from its theorem.
    """
    chunks: list[tuple[str | None, list[str]]] = []
    kind: str | None = None
    buf: list[str] = []
    pending: list[str] = []
    balance = 0

    def flush() -> None:
        nonlocal buf, kind, pending
        if pending:  # balanced attributes not followed by a declaration
            buf = pending + buf
            pending = []
        if buf:
            chunks.append((kind, buf))
        buf = []
        kind = None

    for line in text.splitlines():
        m = DECL_START_RE.match(line) if not line[:1].isspace() else None
        if m:
            flush()
            kind = m.group(1)
            buf = list(pending)
            pending = []
            balance = 0
            buf.append(line)
            continue
        if not line[:1].isspace() and line.lstrip().startswith("@["):
            pending.append(line)
            balance += line.count("[") - line.count("]")
            continue
        if pending:
            if balance > 0:
                pending.append(line)
                balance += line.count("[") - line.count("]")
            else:
                buf.extend(pending)
                pending = []
                buf.append(line)
            continue
        buf.append(line)
    flush()

    out: list[tuple[str | None, str]] = []
    for k, lines in chunks:
        chunk = "\n".join(lines).strip()
        if chunk:
            out.append((k, chunk))
    return out


def _reorder_def_before_lemma(text: str) -> str:
    """Move all ``def`` declarations before ``lemma``/``theorem`` blocks.

    Splits text into top-level declaration chunks (see
    :func:`_decl_chunks`), classifies each as ``def``, ``lemma``, or
    ``other`` (imports, comments, etc.), and re-emits them as: ``other``
    (preserving original order) → ``def`` → ``lemma``.
    """
    others: list[str] = []
    defs: list[str] = []
    lemmas: list[str] = []
    for kind, chunk in _decl_chunks(text):
        if kind == "def":
            defs.append(chunk)
        elif kind in ("lemma", "theorem"):
            lemmas.append(chunk)
        else:
            others.append(chunk)
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


def _select_lemma(
    lemmas: list[tuple[int, str, str]], theorem_name: str | None,
) -> tuple[int, str, str] | None:
    """Pick the main theorem among ``(line, kind, name)`` declarations.

    If ``theorem_name`` is given, find that specific theorem/lemma.
    Otherwise prefer one named ``solution`` (the FLT convention — helpers
    may follow it in the file), falling back to the last theorem/lemma
    (the generic convention: the main result comes after helpers).
    """
    if theorem_name is not None:
        matches = [d for d in lemmas if d[2] == theorem_name]
        return matches[0] if matches else None
    solutions = [d for d in lemmas if d[2] == "solution"]
    if solutions:
        return solutions[0]
    return lemmas[-1] if lemmas else None


def extract_statement_from_text(
    text: str, theorem_name: str | None = None,
) -> tuple[str, str] | None:
    """Extract ``(name, signature)`` from source Lean text.

    If ``theorem_name`` is given, find that specific theorem/lemma.
    Otherwise, prefer ``solution`` (FLT) and fall back to the last
    theorem/lemma in the file (see :func:`_select_lemma`).
    """
    decls = find_declarations(text)
    lemmas = [(i, k, n) for i, k, n in decls if k in ("theorem", "lemma")]
    if not lemmas:
        return None
    target = _select_lemma(lemmas, theorem_name)
    if target is None:
        return None

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
    target = _select_lemma(lemmas, theorem_name)
    if target is None:
        return None

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
    proof = re.sub(r"^by\b\s*", "", proof)
    # Drop trailing interpreter commands (FLT files end with
    # `#print axioms solution`) and surrounding blank lines.
    proof_parts = proof.splitlines()
    while proof_parts and (
        not proof_parts[-1].strip() or proof_parts[-1].lstrip().startswith("#")
    ):
        proof_parts.pop()
    proof = "\n".join(proof_parts).strip()
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

    The separator is the *first* ``:`` at paren/bracket depth 0: theorem
    binders are always bracketed groups (``(…)``/``{…}``/``[…]``), so any
    colon they contain is at depth ≥ 1, whereas the conclusion may contain
    later depth-0 colons inside unbracketed existential binders such as
    ``∃ l : E →L[ℝ] ℝ, P`` (or ``Σ x : α, …``).  Taking the *last* such
    colon, as an earlier version did, split the conclusion at ``∃ l :``.
    Returns ``("", sig)`` if no separator is found.
    """
    open_chars = set("([{⟨⟪")
    close_chars = set(")]}⟩⟫")
    depth = 0
    for i, c in enumerate(sig):
        if c in open_chars:
            depth += 1
        elif c in close_chars:
            depth -= 1
        elif c == ":" and depth == 0:
            binders = sig[:i].rstrip()
            conclusion = sig[i + 1 :].lstrip()
            return (binders, conclusion)
    return ("", sig)


def split_binder_groups(binders: str) -> list[str]:
    """Split a binder string into its top-level ``(..)``/``{..}``/``[..]`` groups."""
    open_chars = set("([{⟨⟪")
    close_chars = set(")]}⟩⟫")
    groups, depth, start = [], 0, None
    for i, c in enumerate(binders):
        if c in open_chars:
            if depth == 0:
                start = i
            depth += 1
        elif c in close_chars:
            depth -= 1
            if depth == 0 and start is not None:
                groups.append(" ".join(binders[start:i + 1].split()))
                start = None
    return groups


def layout_binders(binders: str) -> tuple[str, str]:
    """Lay binders out per AGENTS.md (PORTING RULE 7).

    Returns ``(pre_given, given)``: the text before ``-- given`` and the
    explicit binders after it.  Before ``-- given``, in order:
      1. one line of standalone instances ``[..]`` (no implicit binder here
         declares the variables they mention),
      2. one line per implicit binder ``{..}`` followed by its dependent
         instances ``[..]``,
      3. one line per bare implicit binder (no dependent instance).
    Explicit ``(..)`` binders go after ``-- given`` in source order.  Bare
    ``{E : Type*}`` binders are dropped (autoImplicit).  Lines are 2-indented.
    """
    groups = split_binder_groups(binders)
    implicit = [g for g in groups if g.startswith("{") or g.startswith("⦃")]
    # autoImplicit is on: bare universe binders such as {E : Type*} are dropped;
    # the instances mentioning E bind it implicitly.
    implicit = [g for g in implicit if not re.fullmatch(r"\{[^:]+:\s*(Type|Sort)[^}]*\}", g)]
    inst = [g for g in groups if g.startswith("[")]
    explicit = [g for g in groups if g.startswith("(")]

    def names(g):
        head = g[1:-1].split(":", 1)[0]
        return set(head.split())

    def idents(g):
        return set(re.findall(r"[^\s()\[\]{}:,→∀∃]+", g[1:-1]))

    attached = {i: [] for i in range(len(implicit))}
    standalone = []
    for g in inst:
        used = idents(g)
        hits = [i for i, b in enumerate(implicit) if names(b) & used]
        if hits:
            attached[hits[-1]].append(g)
        else:
            standalone.append(g)

    lines = []
    if standalone:
        lines.append("  " + " ".join(standalone))
    for i, b in enumerate(implicit):
        if attached[i]:
            lines.append("  " + " ".join([b] + attached[i]))
    for i, b in enumerate(implicit):
        if not attached[i]:
            lines.append("  " + b)

    def is_prop(g):
        ty = g[1:-1].split(":", 1)[1] if ":" in g else ""
        return bool(re.search(r"[=≠<>≤≥∈∉→∧∨¬↔]|Continuous|Prop", ty))

    # Source order is kept: later hypotheses depend on earlier variables.
    return "\n".join(lines), " ".join(explicit)


# ---------------------------------------------------------------------------
# Skeleton generation (PORTING RULE 4)
# ---------------------------------------------------------------------------

SOURCE_LABELS = {
    "fermats-last-theorem": "FLT",
    "mathlib4": "Mathlib",
    "mathlib": "Mathlib",
    "rl-theory-in-lean": "RL",
}


def source_link(source_url: str, label: str | None = None) -> str:
    """Return ``[label](url)`` (PORTING RULE 6).

    If *label* is not given it is derived from the repository name in the URL
    (mathlib4 -> Mathlib); for fermats-last-theorem the label is the source
    theorem name (file stem without ``S_``), as in existing FLT ports.
    """
    source_url = source_url.strip()
    m = re.match(r"\[[^\]]+\]\(.+\)$", source_url)
    if m:  # already a markdown link
        return source_url
    if not label:
        m = re.search(r"github\.com/[^/]+/([^/]+)", source_url)
        repo = m.group(1) if m else None
        if repo == "fermats-last-theorem":
            # Existing FLT ports label the link with the source theorem name:
            # the file stem minus ``.lean`` and the leading ``S_``.
            stem = source_url.rstrip("/").rsplit("/", 1)[-1]
            stem = re.sub(r"\.lean$", "", stem)
            label = re.sub(r"^S_", "", stem)
        else:
            label = SOURCE_LABELS.get(repo, repo) if repo else "source"
    return f"[{label}]({source_url})"


def make_skeleton(
    source_url: str | None,
    statement: tuple[str, str] | None,
    proof: str | None = None,
    defs: str = "",
    helpers: str = "",
    date: str = DEFAULT_DATE,
    source_label: str | None = None,
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

    # Rule 7: AGENTS.md layout -- instances/implicits before ``-- given``,
    # explicit binders after it, ``:`` ending the last binder line.
    pre_given, given = layout_binders(binders)
    pre_given_block = pre_given + "\n" if pre_given else ""
    given_line = ("  " + given + " :") if given else None

    proof_body = textwrap.dedent(proof) if proof else "sorry"
    # Proof body is strictly 2-indented under ``-- proof``.
    indented_proof = "\n".join(
        ("  " + line if line.strip() else "") for line in proof_body.splitlines()
    )

    # Source link docstring
    if source_url:
        docstring = f"/--\n{source_link(source_url, source_label)}\n-/"
    else:
        docstring = "/-- ported from external source -/"

    # Build preamble: docstring → defs → helpers (rule 5: def before lemma).
    preamble_parts = [docstring]
    if defs:
        preamble_parts.append(defs)
    if helpers:
        preamble_parts.append(helpers)
    preamble = "\n\n".join(preamble_parts)

    if given_line:
        signature = f"{pre_given_block}-- given\n{given_line}\n-- imply\n"
    else:
        # No explicit binders: ``:`` closes the last binder line.
        pre = pre_given_block.rstrip("\n")
        signature = (f"{pre} :\n" if pre else "  :\n") + "-- imply\n"
    return f"""import Mathlib
import sympy.Basic


{preamble}
@[main]
private lemma main
{signature}  {conclusion} := by
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
            "mjs/lemmaPath.mjs."
        ),
    )
    ap.add_argument(
        "source", nargs="?", default=None,
        help="Source .lean file containing the theorem to port.",
    )
    ap.add_argument("--source-url", default=None,
                    help="Source URL; written as a [label](url) docstring link "
                         "(PORTING RULE 6) marking the theorem as already proven.")
    ap.add_argument("--source-label", default=None,
                    help="Link label (default: theorem name for FLT URLs, else repo label).")
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
        help="Phase 2: run mjs/lemmaPath.mjs --json on existing .lean paths.",
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
        source_label=args.source_label,
    )

    # Derive path (phase 1 rough).
    fallback = fallback_path_for(source, main_name, ported_root)
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
    if not SUGGEST_LEMMAPATH.is_file():
        print(f"ERROR: missing {SUGGEST_LEMMAPATH}", file=sys.stderr)
        return 1
    if not args.paths:
        print(
            "ERROR: --finalize needs one or more Lemma/.../.lean paths",
            file=sys.stderr,
        )
        return 1

    print(f"phase-2 precise : {SUGGEST_LEMMAPATH.name}")
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
        ok = _consistent_ok(result)
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