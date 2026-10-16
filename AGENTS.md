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
    suggest a better lemma path if it isn't consistent
- Attribute-generated lemmas
  - Read `sympy/Basic.lean` to understand attribute-generated lemmas (`@[comm]`, `@[cast]`, `@[mp]`, `@[mpr]`, `@[fin]`, `@[mt]`, …) and apply them wisely.
  - For `LHS.is.RHS` tagged with `@[mp]` / `@[mpr]`, prefer the generated one-direction lemmas `RHS.of.LHS` / `LHS.of.RHS` over calling `.mp` / `.mpr` on the iff.
  - For `LHS.eq.RHS` tagged with `@[comm]`, prefer the generated commutative lemma `RHS.eq.LHS` over `simp [← LHS.eq.RHS]` or `rw [LHS.eq.RHS.symm]`.
- code layout strictly 2-indented
  - `import` / `open` / `set_option` are contiguous (no blank lines between them), then exactly two blank lines before the rest of the file
    - drop unused `open`s by heuristic, not a `run.mjs` warning: from the lemma AST, keep `open NS` only if some identifier would not resolve from the file’s `import`s without that namespace. Do not add a compiler rule (`open-section` / `open-duplicate` / `open-prefix` stay). Keep `open scoped` and opens that only supply instances or notation even when no AST identifier is from that namespace. Mapping an identifier to its defining namespace (`measurable_snd` → `MeasureTheory`) over-requires opens that imports / `export` / Prelude already provide, and drop-one compile is costly; a noisy unused-`open` rule would fail every run until agents delete needed opens.
  - before the `given` section, omit auto-bound implicits
  - within the `given` section: propositions come first, expressions come next, unless otherwise specified
  - within the `proof` section, tactics convention:
    - prefer `apply` instead of `exact`, perhaps by creating some holes
    - inline `have` without introducing `show` if it is referenced only once
    - A sub lemma without @[path], referenced only once, can be inlined if no `have` is introduced
    - use `grind`/`aesop` as much as possible

## Folder layout
- `Lemma/` 
  - it holds only lemmas (`lemma`); these are the public results that get rendered.
  - each sub-folder is a section; a section name must be a math data type, not a type class.
  - check section kind with `node mjs/lemmaSectionKind.mjs` (optional folder names as args); classifies each `Lemma/` subfolder as data type / type class / topic via Mathlib (`Lean.isClass` / `isStructure`).
- `sympy/` holds definitions plus only `theorem`s; these theorems are an internal API used by the definitions and are not rendered publicly. Never put a `lemma` in `sympy/`.


## Sub-agents
- Work on https://github.com/math-proof/lemma.
- Modify only files in your assigned folder (agent name = folder name, e.g. Tensor → `Lemma/Tensor`).
- To modify another folder, send the task to the agent named after that folder (see Inter-agent communication).
- If that agent does not exist, ask `md` (primary) for help.

## Inter-agent communication
This copy-paste path is for **Cursor-like** agents, who cannot talk to other agents. Do not claim you dispatched a job, and do not wait for a colleague that never receives the message.

**Grok** bots can talk to colleagues. They skip this section: send the job to Mr. AgentName directly (do not give the user a paste prompt).

When the user says to send this issue / problem / bug / job / task to **Mr. AgentName** (or “send to AgentName”):
- Write a **self-contained prompt** for that agent (assignee, goal, paths, errors, constraints, follow this `AGENTS.md`).
- Emit that prompt as **exactly one** fenced code block tagged `markdown` (opening line ` ```markdown `, closing ` ``` `). The chat UI must show **exactly one** clickable **copy** control for the whole prompt; the user clicks it instead of selecting text and pressing Ctrl+C.
- **One clickable only:** do not nest other fenced blocks (` ```… `) inside that prompt — each inner fence can add another copy button and the user cannot tell which to use. Put Lean/shell examples inside the prompt as indented plain text (or prose), never as nested triple-backtick fences.
- Never put the prompt in prose, a quote, a list, or several blocks — those have no one-click copy for the whole text.
- After the block, one short line: who it is for and that the user should paste it to that agent.

## Debugging
- print logging info via `sympy.printing.echo` by creating *.echo.lean tracing files for debugging.
- Confirm the file compiles with `lake build <Module.Name>` or `lake env lean <path/to/file.lean>`.

## Git
- Stay on `main`. Do not switch to any other branch; merge changes into `main` instead.
- Work only in `/home/cosmos/src/lean` (same tree as `/home/cosmos/github/lean`). Never edit or commit in `E:\github\lean` / `/mnt/e/github/lean`; the only git command allowed there is `git pull`.
