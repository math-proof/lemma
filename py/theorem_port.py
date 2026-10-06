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
   binders are dropped (autoImplicit binds ``E`` from the instances).
   Everything above ``-- given`` is implicit or instance-implicit ONLY:
   explicit data binders (non-propositions, e.g. ``(n N : ℕ)``,
   ``(f : α → Set β)``) are converted to ``{n N : ℕ}``/``{f : α → Set β}``
   and join the pre-``-- given`` block, one per line, since hypotheses
   reference them.  Only proposition binders stay explicit, under
   ``-- given``, one per line (readability), with
   `` :`` ending the last binder line, e.g.::

       private lemma main
         {t : AddCircle (1 : ℚ)}
         {n N : ℕ}
       -- given
         (hN : 0 < N)
         (hnN : n ∣ N)
         (ht : n • t = 0) :

   Proposition detection: name convention ``h…``, proposition-former head
   (``∀``/``∃``/``Is…``/``Continuous``/…), ``Prop`` type, or a relational
   operator at bracket depth 0.  Plain ``→`` is not a prop signal.
   Exception — promoted instance hypotheses: a Prop-valued instance binder
   ``[T]`` (head segment ``Is…``/``Has…`` or a known property class such as
   ``Continuous``/``Measurable``/``Module.Flat``) that the proof consumes
   EXPLICITLY via ``(inferInstance : T)`` is a hypothesis, not ambient
   structure.  It is rewritten to ``(h : T)`` under ``-- given`` and every
   ``(inferInstance : T)`` in the proof is replaced by ``h`` (names
   ``h``, ``h1``, ``h2``, …).  Non-Prop instances (``[Field k]``) and
   instances used only by typeclass search stay instImplicit.  Applied by
   :func:`promote_infer_instance_hyps`.
   Never put ``{..}``/``[..]`` binders under ``-- given`` and never put the
   ``:`` on its own line.  The proof body is also 2-indented.  Applied by
   :func:`layout_binders`.

8. **Term vs tactic proofs.** A source proof ``:= by …`` keeps tactic mode:
   the skeleton emits ``conclusion := by`` with the body under ``-- proof``.
   A bare term proof ``:= f x`` is emitted as ``conclusion :=`` with the
   term under ``-- proof`` and NO ``by`` (never ``by exact expr``, per
   AGENTS.md).  The extractor returns whether the source used ``by``.
   Applied by :func:`extract_proof_from_text` + :func:`make_skeleton`.

FLT extraction (``S_<key>.lean``)
---------------------------------
Sources from ``fermats-last-theorem`` are parsed with the canonical lean.js
AST parser ``mjs/port_flt_lemma.mjs`` (:func:`parse_flt_solution`) instead
of the regex extractors.  Per FLT's ``PROOF-PATH.md``, ``S_<key>.lean``
proves the ``solution`` theorem and the AST returns its exact
``{imports, namespace, theoremName, binders, conclusion, proof,
proofStyle, key}`` — no signature guessing, no binder reordering, exact
term/``by`` style.  Rules 4–8 are still applied by :func:`make_skeleton`,
which on the AST path keeps shared-universe type binders (``{k G : Type}``)
that regex extraction would wrongly drop.  Regex extraction remains the
fallback when the parser rejects the file.

Rules 1–3 and 5 are applied mechanically by :func:`transform_source`.
Rules 4, 6, 7 and 8 are applied by :func:`make_skeleton` which wraps the main theorem
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
OPEN_LINE_RE = re.compile(r'^[ \t]*open[ \t]+([^\n]+)$', re.MULTILINE)
# FLT P2M.Util: p2m_open "NS1 NS2~alias" / p2m_open_scoped "NS"; skip ``... in`` modifiers.
P2M_OPEN_RE = re.compile(
    r'^[ \t]*p2m_open(_scoped)?[ \t]+"([^"\n]+)"(?!\s+in\b)[^\n]*$',
    re.MULTILINE,
)
THEOREM_TO_LEMMA_RE = re.compile(r'^(\s*)theorem\b')
# Standalone diagnostic commands referencing source declaration names.
DIAGNOSTIC_CMD_RE = re.compile(
    r'^\s*#(print|check|eval|reduce|guard_msgs|guard_expr)\b'
)
# A column-0 top-level command that marks the end of a tactic/term proof:
# the AST proof span runs to EOF and can swallow trailing ``example``/etc.
PROOF_TERMINATOR_RE = re.compile(
    r'^(?:@\[[^\n]*\]\s*)?'
    r'(?:noncomputable\s+|private\s+|protected\s+|partial\s+)*'
    r'(?:example|theorem|lemma|def|abbrev|instance|structure|inductive|'
    r'notation|elab|syntax|macro)\b'
    r'|^(?:end|section|namespace|open|universe|set_option|import)\b|^#'
)


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


# Canonical FLT solution-file parser (lean.js AST).  For ``S_<key>.lean``
# sources this is the authoritative extractor: regex extraction drops
# universe-pinned type binders and can reorder binders past their
# dependencies; the AST returns the exact signature pieces.
SUGGEST_FLT_PARSE = ROOT / "mjs" / "port_flt_lemma.mjs"


def parse_flt_solution(source: Path) -> dict | None:
    """Parse an FLT ``S_<key>.lean`` solution via ``port_flt_lemma.mjs``.

    Returns ``{imports, namespace, theoremName, binders, conclusion, proof,
    proofStyle, key}`` or *None* when the source is not an FLT solution or
    the lean.js parser rejects it (callers fall back to regex extraction).
    """
    if not source.stem.startswith("S_"):
        return None
    proc = subprocess.run(
        ["node", str(SUGGEST_FLT_PARSE), str(source)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        return None
    try:
        data = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return None
    if not isinstance(data, dict) or data.get("binders") is None:
        return None
    return data


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

def _binder_group_names(group: str) -> list[str]:
    """Bound variable names of one binder group (``"{A B : Type*}"``).

    Anonymous binders (``"[CommRing A]"``) return an empty list.
    """
    g = group.strip()
    if len(g) >= 2 and g[0] in "([{⟨⟪" and g[-1] in ")]}⟩⟫":
        g = g[1:-1].strip()
    if ":" not in g:
        return []
    return [
        t for t in g.split(":", 1)[0].split()
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", t)
    ]


def _signature_end_line(lines: list[str], start: int) -> int:
    """Line index of the first ``:=`` that ends a declaration signature."""
    j = start
    while j < len(lines) and ":=" not in lines[j]:
        j += 1
    return min(j, len(lines) - 1)


def _inline_section_variables(text: str) -> str:
    """Inline active ``variable`` binders into each declaration.

    Lean's ``variable (x : α) [Inst α]`` binders are implicitly added to
    every declaration in their section/namespace scope; the scaffold deletes
    the ``variable`` lines, so their binders are inserted explicitly here.
    Groups whose bound names already appear in the declaration's binders are
    skipped (an explicit binder shadows the variable).  Over-approximating
    Lean's name-based filtering is harmless: unused binders are linter
    warnings, not errors, and in-file helper calls apply them fully.
    """
    lines = text.splitlines()
    root_vars: list[str] = []
    frames: list[list[str]] = []
    out: list[str] = []

    def active() -> list[str]:
        res: list[str] = []
        seen: set[str] = set()
        for g in root_vars + [g for f in frames for g in f]:
            if g not in seen:
                seen.add(g)
                res.append(g)
        return res

    i = 0
    while i < len(lines):
        line = lines[i]
        if NAMESPACE_START_RE.match(line) or SECTION_START_RE.match(line):
            frames.append([])
            out.append(line)
            i += 1
            continue
        if END_RE.match(line):
            if frames:
                frames.pop()
            out.append(line)
            i += 1
            continue
        vm = re.match(r"^\s*variable\b\s*(.*)$", line)
        if vm:
            target = frames[-1] if frames else root_vars
            for g in split_binder_groups(vm.group(1)):
                if g not in target:
                    target.append(g)
            i += 1
            continue
        if DECL_START_RE.match(line):
            end = _signature_end_line(lines, i)
            sig = "\n".join(lines[i:end + 1]).split(":=", 1)[0]
            binder_region = split_signature(sig)[0]
            region_norm = " ".join(binder_region.split())
            # Names already *bound* by the declaration's own binders (a mere
            # mention inside an instance type, e.g. ``[Module.Free A B]``, is
            # not a binding and must NOT suppress the ``{A B : Type*}``
            # variable).
            bound: set[str] = set()
            for own in split_binder_groups(binder_region):
                bound.update(_binder_group_names(own))
            add: list[str] = []
            for g in active():
                names = _binder_group_names(g)
                if names:
                    if all(n in bound for n in names):
                        continue
                elif " ".join(g.split()) in region_norm:
                    continue
                add.append(g)
            if add:
                head_m = re.match(
                    r"^(.*?\b(?:def|theorem|lemma)\s+[A-Za-z0-9_.']+)(.*)$",
                    line,
                )
                head, tail = head_m.group(1), head_m.group(2)
                cont_indent = "  "
                for ln in lines[i + 1:end + 1]:
                    cm = re.match(r"^(\s+)\S", ln)
                    if cm:
                        cont_indent = cm.group(1)
                        break
                out.append(head)
                out.extend(f"{cont_indent}{g}" for g in add)
                if tail.strip():
                    out.append(f"{cont_indent}{tail.strip()}")
                i += 1
                while i <= end:
                    out.append(lines[i])
                    i += 1
                continue
        out.append(line)
        i += 1
    return "\n".join(out)


def _local_namespace_names(text: str) -> list[str]:
    return [
        m.group(1)
        for m in re.finditer(r"^\s*namespace\s+([A-Za-z0-9_.']+)", text, re.M)
    ]


def _rewrite_local_ns_refs(
    line: str, ns_names: list[str], decl_names: set[str],
) -> str:
    """Rewrite ``Ns.helper`` to ``helper`` for stripped local namespaces.

    Only the last identifier of a qualified chain is rewritten when it is a
    declaration present in the same file; qualifications of external
    namespaces (e.g. Mathlib's ``CategoryTheory.foo``) are left untouched.
    """
    if not ns_names:
        return line
    alt = "|".join(
        sorted((re.escape(n) for n in ns_names), key=len, reverse=True)
    )
    pat = re.compile(rf"(?<![A-Za-z0-9_.'])(?:{alt})\.([A-Za-z0-9_.']+)")

    def rep(m: re.Match[str]) -> str:
        last = m.group(1).split(".")[-1]
        return last if last in decl_names else m.group(0)

    return pat.sub(rep, line)


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
    # Inline ``variable`` binders while section/namespace scopes are intact.
    text = _inline_section_variables(text)
    lines = text.splitlines()

    # Local declarations (theorem/lemma/def names) and the namespaces that
    # enclose them: after stripping the frames, qualified references such as
    # ``Ws10Flat.helper`` are rewritten to the bare ``helper``.
    decl_names = {n for _, _, n in find_declarations(text)}
    namespace_names = _local_namespace_names(text)

    # --- Rule 1: Remove namespace/end and dedent ---
    transformed: list[str] = []
    # Each removed namespace/section frame contributes a dedent delta that is
    # unknown until its first body line appears: FLT does NOT indent namespace
    # bodies (declarations sit at column 0, proofs at 2), so blindly removing
    # 2 spaces per frame would eat the indentation of the proofs inside.
    frames: list[int | None] = []
    for line in lines:
        stripped = line.lstrip()
        if NAMESPACE_START_RE.match(line) or SECTION_START_RE.match(line):
            frames.append(None)
            continue
        if END_RE.match(line) and frames:
            frames.pop()
            continue
        if frames and stripped:
            indent = len(line) - len(stripped)
            known = sum(d for d in frames if d is not None)
            avail = max(0, indent - known)
            for i, d in enumerate(frames):
                if d is None:
                    take = min(2, avail)
                    frames[i] = take
                    avail -= take
            delta = sum(d for d in frames if d is not None)
            line = " " * max(0, indent - delta) + stripped
        transformed.append(line)

    # --- Rule 2: Remove variable lines ---
    transformed = [l for l in transformed if not VARIABLE_RE.match(l)]

    # Remove diagnostic commands (``#print axioms solution`` and friends):
    # they reference the source theorem name, which never survives porting.
    transformed = [l for l in transformed if not DIAGNOSTIC_CMD_RE.match(l)]

    # --- Rule 3: Convert theorem → private lemma ---
    transformed = [
        THEOREM_TO_LEMMA_RE.sub(r"\1private lemma ", l, count=1)
        for l in transformed
    ]

    # Rewrite references to helpers through the now-stripped namespaces.
    transformed = [
        _rewrite_local_ns_refs(l, namespace_names, decl_names)
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

    Returns ``(proof_text, had_by)``: the text after ``:=`` (or ``:= by``)
    up to the next declaration or end of file, and whether the source used
    tactic mode.  If ``theorem_name`` is given, find that specific
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
    # Remember whether the source proof was tactic-mode (``:= by``); a bare
    # term proof (``:= f x``) is emitted without ``by`` (PORTING RULE 8).
    had_by = bool(re.match(r"^by\b", proof))
    # Strip leading "by" if present (the skeleton re-adds ":= by").
    proof = re.sub(r"^by\b\s*", "", proof)
    # AGENTS.md convention: ``have``/``let`` instead of ``haveI``/``letI``
    # (plain ``have``/``let`` register instances since Lean 4.10+).
    proof = re.sub(r"\bhaveI\b", "have", proof)
    proof = re.sub(r"\bletI\b", "let", proof)
    # Drop trailing interpreter commands (FLT files end with
    # `#print axioms solution`) and surrounding blank lines.
    proof_parts = proof.splitlines()
    while proof_parts and (
        not proof_parts[-1].strip() or proof_parts[-1].lstrip().startswith("#")
    ):
        proof_parts.pop()
    proof = "\n".join(proof_parts).strip()
    return (proof, had_by) if proof else None


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


def layout_binders(binders: str, keep_type_binders: bool = False) -> tuple[str, str]:
    """Lay binders out per AGENTS.md (PORTING RULE 7).

    Returns ``(pre_given, given)``: the text before ``-- given`` and the
    explicit binders after it.  Before ``-- given``, in order:
      1. one line of standalone instances ``[..]`` (no implicit binder here
         declares the variables they mention),
      2. one line per implicit binder ``{..}`` followed by its dependent
         instances ``[..]``,
      3. one line per bare implicit binder (no dependent instance).
    Explicit ``(..)`` binders go after ``-- given`` in source order.
    Anonymous ``{E : Type*}`` binders are dropped (autoImplicit).  When
    ``keep_type_binders`` (the authoritative AST path), a type binder is
    dropped only when it declares a single name re-introduced by a later
    group; multi-name binders such as ``{k G : Type}`` stay — the two names
    share one auto-bound universe that ``Rep.{0}`` style conclusions pin.
    """
    groups = split_binder_groups(binders)

    def is_prop(g):
        """Heuristic: is an explicit ``(..)`` binder a hypothesis (Prop)?

        Hypotheses go under ``-- given``; data binders (e.g. ``(n N : ℕ)``,
        ``(f : α → Set β)``) are converted to implicit ``{..}``.  A binder
        is a proposition iff
          - all its names follow the hypothesis convention ``h…``, or
          - its type head is a proposition former (``∀``/``∃``/``Is…``/
            ``Continuous``/``Measurable``/…), or it is/returns ``Prop``, or
          - its type has a relational operator at bracket depth 0.
        Plain ``→`` is NOT a prop signal: ``α → Set β`` is data.
        """
        inner = g[1:-1]
        if ":" not in inner:
            return False
        head, ty = inner.split(":", 1)
        bnames = head.split()
        if bnames and all(n.startswith("h") for n in bnames):
            return True
        t = ty.strip()
        if t.startswith(("∀", "∃")) or re.match(
            r"^(Is|Continuous|Measurable|Pairwise|Unique|Nonempty|Finite)\b", t
        ):
            return True
        if t == "Prop" or re.search(r"→\s*Prop$", t):
            return True
        depth = 0
        for c in t:
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
            elif depth == 0 and c in "=≠<>≤≥∈∉∣∤~≃≡↔∧∨¬":
                return True
        return False

    # Drop ONLY anonymous universe binders ``{X : Type}``/``Type*``/``Type _}``
    # — autoImplicit rebinds those identically.  Explicit universe pins like
    # ``{k : Type u}`` must be kept: the conclusion's ``Scheme.{u}`` /
    # ``Rep.{0}`` relies on the shared level, and autoImplicit would mint a
    # fresh one.
    type_star_re = re.compile(r"\{(?P<head>[^:]+):\s*(?:Type|Sort)\s*[*_]?\}")

    # Names mentioned anywhere outside a candidate binder's own group decide
    # whether autoImplicit would re-introduce it.
    def mentioned_elsewhere(names, idx):
        for k, g in enumerate(groups):
            if k == idx:
                continue
            body = g[1:-1]
            if any(re.search(rf"(?<![A-Za-z0-9_'.↥↑]){re.escape(n)}(?![A-Za-z0-9_'])", body)
                   for n in names):
                return True
        return False

    # Pool of brace binders in SOURCE ORDER: original ``{..}`` plus explicit
    # data binders ``(..)`` converted to ``{..}`` (everything above
    # ``-- given`` is implicit/instImplicit only).  Propositions stay
    # explicit under ``-- given``.  Anonymous ``Type*`` binders are dropped
    # for autoImplicit; on the AST path multi-name / unmentioned ones stay.
    pool = []  # (source_idx, brace_text)
    props = []
    for i, g in enumerate(groups):
        if g.startswith("{") or g.startswith("⦃"):
            pool.append((i, g))
        elif g.startswith("("):
            if is_prop(g):
                props.append(g)
            else:
                pool.append((i, "{" + g[1:-1] + "}"))

    def keep_type_binder(i, g):
        m = type_star_re.fullmatch(g)
        if not m:
            return True  # universe-pinned or not a plain type binder
        if not keep_type_binders:
            return False
        names = m.group("head").split()
        if len(names) > 1:
            return True  # shared auto-bound universe (e.g. {k G : Type})
        return not mentioned_elsewhere(names, i)

    pool = [(i, g) for i, g in pool if keep_type_binder(i, g)]

    def bnames(g):
        head = g[1:-1].split(":", 1)[0]
        return set(head.split())

    def idents(g):
        # Coercion prefixes (↥Bflat, ↑x) must not hide the binder name.
        body = g[1:-1].replace("↥", " ").replace("↑", " ")
        return set(re.findall(r"[^\s()\[\]{},:→∀∃.]+", body))

    # Attach each instance to the LAST PRECEDING brace binder (source order)
    # whose variables it mentions — e.g. ``(G : Type*) [Group G]`` keeps
    # ``[Group G]`` on the ``{G}`` line, never emitted before it.
    attached = {i: [] for i, _ in pool}
    standalone = []
    for j, g in enumerate(groups):
        if not g.startswith("["):
            continue
        used = idents(g)
        hits = [k for k, (i, b) in enumerate(pool) if i < j and bnames(b) & used]
        if hits:
            attached[pool[hits[-1]][0]].append(g)
        else:
            standalone.append(g)

    lines = []
    if standalone:
        lines.append("  " + " ".join(standalone))
    # One pass in SOURCE ORDER: a binder may depend on an earlier "bare"
    # brace binder (e.g. ``{X : Scheme.{u}} {t : X ⟶ …}``), so never emit
    # instance-bearing lines before preceding bare lines.
    for i, b in pool:
        if attached[i]:
            lines.append("  " + " ".join([b] + attached[i]))
        else:
            lines.append("  " + b)
    return "\n".join(lines), "\n".join("  " + g for g in props)


# ---------------------------------------------------------------------------
# Skeleton generation (PORTING RULE 4)
# ---------------------------------------------------------------------------

# Prop-valued instance heads consumed explicitly become explicit givens.
PROP_INSTANCE_HEADS = {
    "Continuous", "ContinuousOn", "Measurable", "MeasurableSet",
    "AEMeasurable", "StronglyMeasurable", "Pairwise", "Unique", "Nonempty",
    "Finite", "Infinite", "Nontrivial", "Module.Flat", "Module.Finite",
    "Module.Projective", "Module.IsTorsionFree", "Algebra.FiniteType",
    "Algebra.IsIntegral",
}


def _prop_instance_type(t: str) -> bool:
    toks = t.split()
    if not toks:
        return False
    head = toks[0]
    last = head.rsplit(".", 1)[-1]
    if last.startswith(("Is", "Has")):
        return True
    return head in PROP_INSTANCE_HEADS


def promote_infer_instance_hyps(binders: str, proof: str) -> tuple[str, str]:
    """[T] consumed via ``(inferInstance : T)`` in the proof becomes
    ``(h : T)`` under ``-- given``; proof occurrences are rewritten to ``h``.
    Non-Prop instances and instances used only by search are untouched."""
    if not binders or not proof:
        return binders, proof
    groups = split_binder_groups(binders)
    norm = lambda s: " ".join(s.split())
    targets: dict[str, int] = {}
    for i, g in enumerate(groups):
        if g.startswith("["):
            t = g[1:-1].strip()
            if _prop_instance_type(t):
                targets[norm(t)] = i

    spans: list[tuple[int, int, str]] = []
    needle = "(inferInstance"
    start = 0
    while True:
        j = proof.find(needle, start)
        if j < 0:
            break
        start = j + 1
        depth = 0
        k = j
        colon = -1
        while k < len(proof):
            c = proof[k]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
                if depth == 0:
                    break
            elif c == ":" and depth == 1:
                colon = k
            k += 1
        if depth != 0 or colon < 0:
            continue
        ty = proof[colon + 1:k].strip()
        if norm(ty) in targets:
            spans.append((j, k + 1, norm(ty)))

    if not spans:
        return binders, proof

    name_of: dict[str, str] = {}
    counter = 0

    def fresh_name() -> str:
        nonlocal counter
        n = "h" if counter == 0 else f"h{counter}"
        counter += 1
        return n

    new_groups = list(groups)
    for ty, idx in targets.items():
        if any(t == ty for _, _, t in spans):
            name_of[ty] = fresh_name()
            new_groups[idx] = f"({name_of[ty]} : {groups[idx][1:-1]})"
    new_binders = " ".join(new_groups)

    out = proof
    for lo, hi, ty in sorted(spans, reverse=True):
        out = out[:lo] + name_of[ty] + out[hi:]
    return new_binders, out


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


def extract_opens(text: str) -> str:
    """Collect ``open`` command lines the source relied on.

    Identifiers that resolved via an ``open`` in the source (e.g.
    ``open groupCohomology`` making ``inhomogeneousCochains`` visible)
    fail as unknown identifiers in the skeleton unless the open is
    preserved.  Emitted after the imports; prune later with
    ``delete_open.*`` per AGENTS.md.

    Lines ending in ``in`` are command modifiers (``open Foo in <cmd>``)
    scoping a single source declaration that is not ported — skipped.

    FLT's ``P2M.Util`` also provides ``p2m_open "A B~h1~h2"`` (equivalent to
    ``open A B (h1 h2)`` — ``~`` separates a namespace from its aliased names)
    and ``p2m_open_scoped "A"`` (``open scoped A``).  Words naming the source
    file's private ``P2MW.S_*`` namespace are dropped: that namespace exists
    only inside the unported source.
    """
    seen: list[str] = []
    for m in OPEN_LINE_RE.finditer(text):
        body = m.group(1).strip()
        if body == "in" or body.endswith(" in"):
            continue
        line = f"open {body}"
        if line not in seen:
            seen.append(line)

    def p2m_words(s: str) -> str:
        out: list[str] = []
        for w in s.split():
            parts = w.split("~")
            ns = parts[0]
            if ns.startswith("P2MW."):
                continue
            hidden = [h for h in parts[1:] if h]
            out.append(ns + (f" ({' '.join(hidden)})" if hidden else ""))
        return " ".join(out)

    for m in P2M_OPEN_RE.finditer(text):
        body = p2m_words(m.group(2))
        if not body:
            continue
        line = ("open scoped " if m.group(1) else "open ") + body
        if line not in seen:
            seen.append(line)
    return "\n".join(seen)


def make_skeleton(
    source_url: str | None,
    statement: tuple[str, str] | None,
    proof: str | None = None,
    defs: str = "",
    helpers: str = "",
    date: str = DEFAULT_DATE,
    source_label: str | None = None,
    proof_tactic: bool = True,
    opens: str = "",
    keep_type_binders: bool = False,
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

    # A Prop-valued instance consumed explicitly via ``(inferInstance : T)``
    # in the proof is a hypothesis: promote its ``[T]`` binder to ``(h : T)``
    # and rewrite the proof to use the name.
    binders, proof = promote_infer_instance_hyps(binders, proof or "")

    # Rule 7: AGENTS.md layout -- instances/implicits before ``-- given``,
    # explicit binders after it, ``:`` ending the last binder line.
    pre_given, given = layout_binders(binders, keep_type_binders=keep_type_binders)
    pre_given_block = pre_given + "\n" if pre_given else ""
    # ``given`` is already one 2-indented line per explicit binder;
    # ``:`` ends the last binder line.
    given_line = (given + " :") if given else None

    proof_body = textwrap.dedent(proof) if proof else "sorry"
    # Tactic proofs follow ``:= by``; term proofs follow a bare ``:=``
    # (PORTING RULE 8 — no ``by exact expr``).
    proof_head = " by" if proof_tactic else ""
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
    open_block = f"\n{opens}\n" if opens else "\n"
    return f"""import Mathlib
import sympy.Basic
{open_block}
{preamble}
@[main]
private lemma main
{signature}  {conclusion} :={proof_head}
-- proof
{indented_proof}


-- created on {date}
"""


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def find_existing_port(source: Path, ported_root: Path) -> Path | None:
    """Return the ``Lemma/…`` file that already ports ``source``, if any.

    A ported file is recognised by the source file name appearing in its
    docstring link (PORTING RULE 6), e.g. ``S_<key>.lean``.  Falls back to a
    ``git grep``-style scan of the ported tree; returns the first match.
    """
    needle = source.name  # e.g. S_AddChar_foo.lean
    try:
        proc = subprocess.run(
            ["grep", "-rl", "-F", needle, str(ported_root)],
            capture_output=True, text=True, timeout=120,
        )
        for hit in proc.stdout.splitlines():
            hit = hit.strip()
            if hit.endswith(".lean") and ".echo." not in hit:
                return Path(hit)
    except Exception:  # noqa: BLE001 — best-effort guard
        pass
    return None




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

    raw_text = source.read_text(encoding="utf-8", errors="replace")

    # Apply porting rules (1, 2, 3, 5) unless --no-transform.
    text = raw_text
    if not args.no_transform:
        text = transform_source(text)

    # FLT ``S_<key>.lean`` solutions: prefer the canonical lean.js AST
    # extractor (mjs/port_flt_lemma.mjs) over regexes.  The AST returns the
    # exact binders / conclusion / proof / proofStyle, avoiding dropped
    # universe-pinned type binders and binder reordering.  Fall back to
    # regex extraction when the parser rejects the file.
    flt = None if args.theorem_name else parse_flt_solution(source)
    if flt is not None:
        main_name = flt.get("theoremName") or "solution"
        sig = f'{flt["binders"].strip()} : {flt["conclusion"].strip()}'
        statement = (main_name, sig)
        # The AST proof span runs to EOF, so trailing commands such as
        # ``#print axioms solution`` or a trailing ``example := solution f``
        # get swallowed into the proof — drop diagnostics and truncate at the
        # first column-0 top-level command that starts a new declaration.
        ns_names = _local_namespace_names(raw_text)
        raw_decl_names = {n for _, _, n in find_declarations(raw_text)}
        proof_lines: list[str] = []
        for i, l in enumerate((flt.get("proof") or "").splitlines()):
            if DIAGNOSTIC_CMD_RE.match(l):
                continue
            if i > 0 and PROOF_TERMINATOR_RE.match(l):
                break
            proof_lines.append(
                _rewrite_local_ns_refs(l, ns_names, raw_decl_names)
            )
        proof = "\n".join(proof_lines).rstrip() or None
        proof_tactic = flt.get("proofStyle", "by") == "by"
    else:
        # Extract the main statement and proof.
        statement = extract_statement_from_text(text, args.theorem_name)
        if statement is None:
            print(f"ERROR: no theorem/lemma found in {source}", file=sys.stderr)
            return 1
        main_name = statement[0]
        extracted = extract_proof_from_text(text, args.theorem_name)
        proof, proof_tactic = extracted if extracted is not None else (None, True)

    # Extract defs and helpers (rule 5: before main lemma).
    defs, helpers = extract_defs_and_helpers(text, main_name)

    # Auto-derive the source URL for known repos (rule 6) when not given.
    source_url = args.source_url
    if source_url is None:
        parts = source.resolve().parts
        if "fermats-last-theorem" in parts:
            i = parts.index("fermats-last-theorem")
            rel = "/".join(parts[i + 1:])
            source_url = (
                "https://github.com/anthropics/fermats-last-theorem"
                f"/blob/main/{rel}"
            )

    # Build the skeleton (rule 4: @[main] private lemma main).
    skeleton = make_skeleton(
        source_url, statement, proof, defs, helpers, args.date,
        source_label=args.source_label, proof_tactic=proof_tactic,
        opens=extract_opens(text), keep_type_binders=flt is not None,
    )

    # Duplicate guard: an existing Lemma file whose docstring links back to
    # this source file means the theorem was already ported (possibly at a
    # different path or as an iff).  Search before spending time on paths.
    existing = find_existing_port(source, ported_root)
    if existing is not None:
        print(f"SKIP (already ported): {existing}")
        return 0

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