# LLM-Assisted Proving

Guidelines and prompts for using LLMs to write and refactor Lean 4 proofs in this repository.

## Proof style
- execute the scripts below
  - mjs/run.mjs
    Besides Lean errors it prints style warnings `warning:LINE:COL: [rule-id] … (AGENTS.md: "…")` for the style rules the compiler checks (layout, binder order, sections, tactics, dates, `open`, attribute docstrings). Fix every warning and re-run until none remain; only leave one if it is a false positive, and name its rule id in your summary. Warnings never fail the run or change the saved lemma.
  - py/delete_import.py
    simplify `import` statements
  - mjs/lemmaPath.mjs
    suggest a better lemma path if it isn't consistent
- Attribute-generated lemmas
  - Read `sympy/Basic.lean` to understand attribute-generated lemmas (`@[comm]`, `@[cast]`, `@[mp]`, `@[mpr]`, `@[fin]`, `@[mt]`, …) and apply them wisely.
  - For `LHS.is.RHS` tagged with `@[mp]` / `@[mpr]`, prefer the generated one-direction lemmas `RHS.of.LHS` / `LHS.of.RHS` over calling `.mp` / `.mpr` on the iff.
  - For `LHS.eq.RHS` tagged with `@[comm]`, prefer the generated commutative lemma `RHS.eq.LHS` over `simp [← LHS.eq.RHS]` or `rw [LHS.eq.RHS.symm]`.
- code layout strictly 2-indented
  - before the `given` section, omit auto-bound implicits
  - within the `given` section: propositions come first, expressions come next, unless otherwise specified
  - within the `proof` section, tactics convention:
    - prefer `apply` instead of `exact`, perhaps by creating some holes
    - inline `have` without introducing `show` if it is referenced only once
    - use `grind`/`aesop` as much as possible

## Folder layout
- `Lemma/` holds only lemmas (`lemma`); these are the public results that get rendered.
- `sympy/` holds definitions plus only `theorem`s; these theorems are an internal API used by the definitions and are not rendered publicly. Never put a `lemma` in `sympy/`.

## Debugging
- print logging info via `sympy.printing.echo` by creating *.echo.lean tracing files for debugging.
- Confirm the file compiles with `lake build <Module.Name>` or `lake env lean <path/to/file.lean>`.

## Git
- Stay on `main`. Do not switch to any other branch; merge changes into `main` instead.
