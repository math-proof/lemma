# Lemma

## Folder rules
- `Lemma/` holds only lemmas (`lemma`); these are the public results that get rendered.
- `instance` / `class` / `structure` / `macro` / `syntax` declarations are not allowed in `Lemma/` files.
- each sub-folder is a section; a section name must be a math data type, not a type class.
- check section kind with `node mjs/lemmaSectionKind.mjs` (optional folder names as args); classifies each `Lemma/` subfolder as data type / type class / topic via Mathlib (`Lean.isClass` / `isStructure`).

## Lemma Proof style

Applies to every `lemma` / `theorem` source in this repository. Agents under `Lemma/` inherit this together with the root [`AGENTS.md`](../AGENTS.md); `Theorem/` (and other decl libraries) reference this file instead of duplicating it.

- execute the scripts below
  - mjs/run.mjs
    Besides Lean errors it prints style warnings `warning:LINE:COL: [rule-id] … (AGENTS.md: "…")` for the style rules the compiler checks (layout, binder order, sections, tactics, dates, `open`, attribute docstrings). Fix every warning and re-run until none remain; only leave one if it is a false positive, and name its rule id in your summary. Warnings never fail the run or change the saved lemma.
  - py/delete_import.py
    simplify `import` statements
  - py/docstring.py
    add attribute docstrings for `@[path, ...]` private lemma main
  - mjs/lemmaPath.mjs
    suggest a better lemma path if it isn't consistent; use `sh/rename.sh` to rename the Lean lemma module if demanded
  - sh/delete.sh
    this script maintains inverted-index table, don't delete lemma/theorem files manually
- Attribute-generated lemmas
  - Read `Initialize/Tactic/Attr/Basic.lean` to understand attribute-generated lemmas (`@[comm]`, `@[cast]`, `@[mp]`, `@[mpr]`, `@[fin]`, `@[mt]`, …) and apply them wisely.
  - For `LHS.is.RHS` tagged with `@[mp]` / `@[mpr]`, prefer the generated one-direction lemmas `RHS.of.LHS` / `LHS.of.RHS` over calling `.mp` / `.mpr` on the iff.
  - For `LHS.eq.RHS` tagged with `@[comm]`, prefer the generated commutative lemma `RHS.eq.LHS` over `simp [← LHS.eq.RHS]` or `rw [LHS.eq.RHS.symm]`.
- code layout strictly 2-indented
  - `import` / `open` / `set_option` are contiguous (no blank lines between them), then exactly two blank lines before the rest of the file
    - drop unused `open`s by heuristic, not a `run.mjs` warning: from the lemma AST, keep `open NS` only if some identifier would not resolve from the file’s `import`s without that namespace. Do not add a compiler rule (`open-section` / `open-duplicate` / `open-prefix` stay). Keep `open scoped` and opens that only supply instances or notation even when no AST identifier is from that namespace. Mapping an identifier to its defining namespace (`measurable_snd` → `MeasureTheory`) over-requires opens that imports / `export` / Prelude already provide, and drop-one compile is costly; a noisy unused-`open` rule would fail every run until agents delete needed opens.
    - drop redundant type ascriptions `(v : T)` by heuristic, not a `run.mjs` warning or Lean linter (both forms elaborate; the compiler cannot flag them). Drop when `v` already has type `T`, or a coercion fills the expected type anyway (`Fin`→`ℕ`, `ℕ`→`ℂ` at `*`, `n - e` with `e : Fin`). Same heuristic for redundant `↑` / Coe: drop when Lean inserts it by typeclass heuristics and the expected type is already clear (e.g. `ℝ*` / Hyperreal).
    - in lemma docstrings which is treated as markdown text:
      - convert raw lemma module/path names to markdown links by heuristic, write lemma module path in the form of a link: `[lemma latex formula or natural language name](?module=Module.Path)`.
      - use `\(...\)` for inline math and `\[...\]` for display math. The renderer does not support `$...$` or `$$...$$`. For example, write `\((X_r, Y_r)\)` for an inline ordered pair.
      - don't paste lean code in docstring.
  - before the `given` section, omit auto-bound implicits
  - explicit binders `(…)` (hypotheses and given-section expressions) sit under `-- given`; type binders `{…}` / `⦃…⦄` and instance binders `[…]` stay above it
  - never `(h : … := by infer_instance)` or any `(h : T := by tactic)`
  - within the `given` section: propositions come first, expressions come next, unless otherwise specified
  - within the `proof` section, tactics convention:
    - prefer `apply` instead of `exact`, perhaps by creating some holes
    - inline `have` without introducing `show` if it is referenced only once
    - A sub lemma without @[path], referenced only once, can be inlined if no extra `have` is introduced
    - delete `classical` when redundant (proof/def still elaborates and builds without it)
    - use `grind`/`aesop` as much as possible
    - Prefer `√` (Root.sqrt notation) over `Real.sqrt` at call sites when both mean the same thing.
  - `set_option maxHeartbeats` (and other elaborator heartbeat budgets) may be set or raised to any value strictly below 1000000. 1000000 and above stay disallowed.
  - Dates: never change `-- created on` even after `sh/rename.sh` / path moves. Only bump `-- updated on` when you edit the lemma. 

## Debugging
- print logging info via `Syntax.Tactic.Echo` by creating *.echo.lean tracing files for debugging.
- Confirm the file compiles with `lake build <Module.Name>` or `lake env lean <path/to/file.lean>`.
