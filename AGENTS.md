# LLM-Assisted Proving

Guidelines and prompts for using LLMs to write and refactor Lean 4 proofs in this repository.

## Proof style
- Attribute-generated lemmas
  - Read `sympy/Basic.lean` to understand attribute-generated lemmas (`@[comm]`, `@[cast]`, `@[mp]`, `@[mpr]`, `@[fin]`, `@[mt]`, …) and apply them wisely.
  - For `LHS.is.RHS` tagged with `@[mp]` / `@[mpr]`, prefer the generated one-direction lemmas `RHS.of.LHS` / `LHS.of.RHS` over calling `.mp` / `.mpr` on the iff.
  - For `LHS.eq.RHS` tagged with `@[comm]`, prefer the generated commutative lemma `RHS.eq.LHS` over `simp [← LHS.eq.RHS]` or `rw [LHS.eq.RHS.symm]`.
  - Run `python py/docstring.py <leanFile>` if necessary. It'll generate the attribute docstring table if the lemma uses attributes other than `@[main]`.
- code layout strictly 2-indented
  - before the `given` section, list in order:
    - line(s) of standalone instances (instImplicit)
    - line(s) of implicit binder(s) and their dependent instances (instImplicit) on the same line, if any
    - line(s) of bare implicit binders
  - default arguments should be put within the `given` section: propositions come first, expressions come next, unless otherwise specified
  - conclusion must be put within the `imply` section
  - proof body must be put within the `proof` section, within proof:
    - binary operators below should not be indented by new lines:
      - `:`, e.g., (ident : Type) 
      - arithmetic operators: `+` `-` `*` `/` 
      - relational operators: `=` `≠` `>` `<` `≥` `≤` 
    - After a bullet tactic (`·`), put the next statement on a new line when that branch contains more than one step.
    - tactics convention:
      - Use `obtain` instead of `rcases`, `if … then … else …` instead of `by_cases` (if it is not followed by `<;>`), `have` instead of `haveI`, and `let` instead of `letI`.
      - inline `have` without introducing `show` if it is referenced only once, e.g.: prefer `apply` instead of `exact`, perhaps by creating some holes.
      - use `calc` instead of `by calc`, start `calc` with `_`
      - avoid `calc` within [] block of `rw`/`erw`/`simp`, or within () as arguments;
      - no multi-line tactics inside parentheses, the tactic within compact type-ascribed `by` term (by tactic : Type) should be one-liner with no `;`
      - follow `show` with `from`/`by` instead of `from by`
      - `by exact expr` should be simplifed to `expr`
      - use `grind`/`aesop` as much as possible
      - in `apply`/`exact`, use `_` as arguments as much as possible, prefer `_` instead of `?_`/`?identifier`
  - date created must be today, if date updated is the same as date created, it should be omitted.
- [lemma path](mjs/README.md)
  - it conveys the lemma semantic per se, thus facilitating search
  - it must be consistent with what is suggested by mjs/lemmaPath.mjs
- `import` statements
  - check py/delete_import.py to simplify `import` statements
- `open` statements
  - check delete_open.* to simplify `open` statements
  - use `open Section` if lemmas from that Section are imported


## Debugging
- print logging info via `sympy.printing.echo` by creating *.echo.lean tracing files for debugging.
- Confirm the file compiles with `lake build <Module.Name>` or `lake env lean <path/to/file.lean>`.
