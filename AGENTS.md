# LLM-Assisted Proving

Guidelines and prompts for using LLMs to write and refactor Lean 4 proofs in this repository.

## Lemma Proof style
- execute the scripts below
  - mjs/run.mjs
    Besides Lean errors it prints style warnings `warning:LINE:COL: [rule-id] … (AGENTS.md: "…")` for the style rules the compiler checks (layout, binder order, sections, tactics, dates, `open`, attribute docstrings). Fix every warning and re-run until none remain; only leave one if it is a false positive, and name its rule id in your summary. Warnings never fail the run or change the saved lemma.
  - py/delete_import.py
    simplify `import` statements
  - py/docstring.py
    add attribute docstrings for `@[path, ...]` private lemma main
  - mjs/lemmaPath.mjs
    suggest a better lemma path if it isn't consistent; use `sh/rename.sh` to rename the Lean lemma module
- Attribute-generated lemmas
  - Read `sympy/Basic.lean` to understand attribute-generated lemmas (`@[comm]`, `@[cast]`, `@[mp]`, `@[mpr]`, `@[fin]`, `@[mt]`, …) and apply them wisely.
  - For `LHS.is.RHS` tagged with `@[mp]` / `@[mpr]`, prefer the generated one-direction lemmas `RHS.of.LHS` / `LHS.of.RHS` over calling `.mp` / `.mpr` on the iff.
  - For `LHS.eq.RHS` tagged with `@[comm]`, prefer the generated commutative lemma `RHS.eq.LHS` over `simp [← LHS.eq.RHS]` or `rw [LHS.eq.RHS.symm]`.
- code layout strictly 2-indented
  - `import` / `open` / `set_option` are contiguous (no blank lines between them), then exactly two blank lines before the rest of the file
    - drop unused `open`s by heuristic, not a `run.mjs` warning: from the lemma AST, keep `open NS` only if some identifier would not resolve from the file’s `import`s without that namespace. Do not add a compiler rule (`open-section` / `open-duplicate` / `open-prefix` stay). Keep `open scoped` and opens that only supply instances or notation even when no AST identifier is from that namespace. Mapping an identifier to its defining namespace (`measurable_snd` → `MeasureTheory`) over-requires opens that imports / `export` / Prelude already provide, and drop-one compile is costly; a noisy unused-`open` rule would fail every run until agents delete needed opens.
    - drop redundant type ascriptions `(v : T)` by heuristic, not a `run.mjs` warning or Lean linter (both forms elaborate; the compiler cannot flag them). Drop when `v` already has type `T`, or a coercion fills the expected type anyway (`Fin`→`ℕ`, `ℕ`→`ℂ` at `*`, `n - e` with `e : Fin`). Keep ascriptions that pick a numeral’s type (`(0 : ℂ)`), that state a `show` used as a rewrite (`show ((1 : Fin 3) : ℕ) = 1`), or that the file fails to elaborate without.
  - before the `given` section, omit auto-bound implicits
  - explicit binders `(…)` (hypotheses and given-section expressions) sit under `-- given`; type binders `{…}` / `⦃…⦄` and instance binders `[…]` stay above it
  - an instance binder that a later given hypothesis needs stays an instance binder `[instImplicit]` inside `-- given`, before that hypothesis; never `(h : … := by infer_instance)` or any `(h : T := by tactic)`
  - within the `given` section: propositions come first, expressions come next, unless otherwise specified
  - within the `proof` section, tactics convention:
    - prefer `apply` instead of `exact`, perhaps by creating some holes
    - inline `have` without introducing `show` if it is referenced only once
    - A sub lemma without @[path], referenced only once, can be inlined if no `have` is introduced
    - delete `classical` when redundant (proof/def still elaborates and builds without it)
    - use `grind`/`aesop` as much as possible
  - `set_option maxHeartbeats` (and other elaborator heartbeat budgets) may be set or raised to any value strictly below 1000000. 1000000 and above stay disallowed.
  - Dates: never change `-- created on` (including after `sh/rename.sh` / path moves). Only bump `-- updated on` when you edit the lemma. A `[date-created-today]` warning on a rename is a linter false positive if created was rewritten — restore the original created date; do not set created to today.

## Folder layout
- `Lemma/` 
  - it holds only lemmas (`lemma`); these are the public results that get rendered.
  - `instance` / `class` / `structure` / `macro` / `syntax` declarations are not allowed in `Lemma/` files.
  - each sub-folder is a section; a section name must be a math data type, not a type class.
  - check section kind with `node mjs/lemmaSectionKind.mjs` (optional folder names as args); classifies each `Lemma/` subfolder as data type / type class / topic via Mathlib (`Lean.isClass` / `isStructure`).
- `Syntax/` holds user-defined `syntax` / related elaborator declarations. Do not put those in `sympy/` or `Lemma/`.
- Decl libraries (siblings of `Syntax/`): `Def/` (`def`), `Abbrev/` (`abbrev`), `Class/` (`class`), `Structure/` (`structure`), `Inductive/` (`inductive`), `Instance/` (`instance`), `Notation/` (`notation` / infix-family), `Macro/` (`macro`), `Theorem/` (`theorem`).
- `Theorem/` holds utility `theorem`s with attributes **other than** `@[main]` (helpers / internal API; not public rendered lemmas). Do not put `@[main]` results or `lemma`s here — those stay in `Lemma/`.
- `sympy/` holds definitions (plus theorems only when tightly tied to those defs). Prefer `Theorem/` for utility theorems with non-`@[main]` attributes. Never put a `lemma` or user-defined syntax in `sympy/`.
- Scratch/temp files (probes, bisect scripts, ad-hoc `tmp_*` / `probe_*` / `test_*` files) live in the gitignored `tmp/` folder, not at the repo root.


## Sub-agents
- Work on https://github.com/math-proof/lemma.
- Modify only files in your assigned folder (agent name = folder name, e.g. Tensor → `Lemma/Tensor`).
- To modify another folder, send the task to the agent named after that folder (see Inter-agent communication).
- If that agent does not exist, ask `md` (primary) for help.

## Inter-agent communication
This copy-paste path is for **Cursor-like** agents, who cannot talk to other agents. Do not claim you dispatched a job, and do not wait for a colleague that never receives the message.

**Grok** bots can talk to colleagues. They skip this section: send the job to @AgentName directly (do not give the user a paste prompt).

When the user says to send this issue / problem / bug / job / task to **@AgentName** (or “send to AgentName”):
- Write a **self-contained prompt** for that agent (assignee, goal, paths, errors, constraints, follow this `AGENTS.md`).
- Emit that prompt as **exactly one** fenced code block tagged `markdown` (opening line ` ```markdown `, closing ` ``` `). The chat UI must show **exactly one** clickable **copy** control for the whole prompt; the user clicks it instead of selecting text and pressing Ctrl+C.
- **One clickable only:** do not nest other fenced blocks (` ```… `) inside that prompt — each inner fence can add another copy button and the user cannot tell which to use. Put Lean/shell examples inside the prompt as indented plain text (or prose), never as nested triple-backtick fences.
- Never put the prompt in prose, a quote, a list, or several blocks — those have no one-click copy for the whole text.
- Prompt shape (first line and sections): open with
  `Assignee: AgentName (scope; this chat id <uuid>). Follow AGENTS.md; …`
  then `## Goal`, repro/paths/errors, constraints. Include the target agent **chat id** in Assignee when the user gave it (or when known).
- After the block, one short line telling the user to paste into that agent chat, naming the subagent as a markdown link:
  `[<path-or-scope> / AgentName](<chat-id>)`
  Example: `[lemmaPath / mjs](dfdec45a-5321-428c-9160-f3c47ec2af53)` — short scope or file path, then `/`, then the agent name; the link target is the agent **chat id** (UUID). Prefer this over bare `@AgentName` when a chat id is available.

## Debugging
- print logging info via `sympy.printing.echo` by creating *.echo.lean tracing files for debugging.
- Confirm the file compiles with `lake build <Module.Name>` or `lake env lean <path/to/file.lean>`.

## Git
- Stay on `main`. Do not switch to any other branch; merge changes into `main` instead.
- Work only in `/home/cosmos/github/lean`. Never edit or commit in `E:\github\lean` / `/mnt/e/github/lean`; the only git command allowed there is `git pull`.
