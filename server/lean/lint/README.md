# Lemma linter (`server/lean/lint/`)

The mechanically checkable style rules of `AGENTS.md`, reported as **warnings** (never errors) by the compiler:

- `render2vue.mjs` `echo2vueFromSource` → `code.warning` (only when non-empty), so they show up in the
  `php/request/echo.php` JSON and in `node mjs/run.mjs <file>` (stderr, `warning:LINE:COL: [rule-id] … (AGENTS.md: "…")`).
- They never change the lemma status, `run.mjs`'s exit code, or the `axiom.lemma` row (`warning` is not a saved column).

Two passes:

- **Text scan** (most rules): the source with comments / strings blanked (`scan.mjs`), a bracket matcher, and a small
  binder-signature parser. Reports `line` / `col`.
- **AST pass** (`astRules.mjs`): the file is parsed with lean.js (`compile`, the same parser as the renderer; a separate
  tree, since `echo` mutates it). The tree has no source positions, so these warnings **quote the offending statement**
  instead: `w.stmt` is the node's own reprint (`String(node)`), trimmed to its first line(s) / ~120 chars with `…`.
  `w.line` is filled in by searching the source for that text (forward cursor in source order, re-anchored at each
  declaration; a repeated statement text resolves to its next occurrence). `run.mjs` prints

  ```
  warning:23: [have-inline-once] `h₁` is used only once, by the next `exact`: … (AGENTS.md: "…")
      > have h₁ : n = n := by
      >   simp
  ```

  If the parse throws, the AST rules are skipped silently and their text-scan versions run instead (`AST_RULES` /
  `ctx.astCovered`), so a rule never reports twice. Layout rules (bullets, indentation, line breaks around operators)
  stay text-based: the reprint normalizes layout.

| AST rule | how the tree is used | text fallback |
|---|---|---|
| `have-inline-once` | `Lean_have` in a statement list (`LeanStatements`, or the list after a bare `·` line); the next statement is a `LeanTactic` `exact` / `apply` without `LeanAt`; the name occurs as a `LeanToken` exactly once there and nowhere else in the rest of the block (until rebound) | `proofRules.mjs` |
| `given-prop-first` | binders after `-- given`; proposition = type node is a relation / connective / quantifier / negation (`LeanBinaryBoolean`, `LeanQuantifier`, `LeanNot`, …) or an `h…` name; expression = a type token / arrow / applied type not headed by a predicate (`Is…`, `Continuous`, `Measurable`, …); never a proposition when headed by `Decidable`/`Fintype`/`Set`/…; warns when a proposition mentions none of the names bound from the expression up to itself (so it can really move up) | `signatureRules.mjs` |
| `tactic-haveI`, `tactic-letI` | `Lean_have` / `Lean_let` with the parser flag `inst` (parsed from `haveI` / `letI`), outside declaration signatures | `proofRules.mjs` |
| `calc-after-assign` | `have` / `let` (incl. `haveI` / `letI`) whose `:=` value is a `LeanArgsNewLineSeparated` holding only a `LeanCalc`, i.e. `:=⏎ calc`; the same-line form `:= calc` has the `LeanCalc` itself as the value. Not an AGENTS.md rule (no quote) | — (AST only) |

| file | rules |
|---|---|
| `headerRules.mjs` | `open-section`, `open-duplicate`, `open-unused` (off by default), `open-prefix`, `attr-docstring`, `date-*` |
| `signatureRules.mjs` | `section-imply`, `section-proof`, `binder-order`, `binder-dep-inst`, `binder-auto-bound`, `default-arg-given`, `given-prop-first`, `binder-combine` |
| `proofRules.mjs` | `indent-odd`, `indent-deep`, `proof-binop-newline`, `bullet-newline`, `tactic-rcases`, `tactic-by-cases`, `tactic-haveI`, `tactic-letI`, `have-inline-once`, `by-calc`, `calc-start-underscore`, `calc-in-brackets`, `paren-by-multiline`, `paren-by-semicolon`, `from-by`, `by-exact`, `hole-question`, `binder-underscore-name` |
| `attrRules.mjs` | `attr-mp`, `attr-comm` (read the cited lemma's `@[…]` from `Lemma/…`) |
| `astRules.mjs` | `have-inline-once`, `given-prop-first`, `tactic-haveI`, `tactic-letI` (text versions above are their fallbacks), `calc-after-assign` |

`open-prefix` (text scan): when `open Random` (plain, not selective/`scoped`) and the source
writes `Random.Foo.Bar`, warn to drop the leading `Random.` **only if** (1) `Lemma/Random/Foo/Bar.lean`
exists (filesystem resolve; attribute-generated names with no `.lean` are skipped) and (2) no other
currently open section (plus the file's own `Lemma/<Section>/`) also has a lemma at that short path.
Quoted as `stmt: Random.Foo.Bar`. AGENTS.md has no exact bullet yet — the warning paraphrases the
open-simplification idea (`after \`open Section\`, prefer the short lemma name when unambiguous`).

`RULES` in `index.mjs` maps every id to the quoted AGENTS.md rule; `DISABLED` lists rules that are off by default
(`lintLean(src, { rules: ['open-unused'] })` still runs them).

Offline: `lintLean(source, { file, root, sections, today, isNew, ast })` (`ast: false` forces the text fallbacks); `lintLeanFile(source, abs)` derives `root` / `file`
from the path and `isNew` from a read-only `git status` (for `date-created-today`).

Known limits of the AST pass (false negatives only): a few constructs make the parser nest statements wrongly — a
multi-line `exact` can split into siblings, `{ … with … }` structure instances — so `have-inline-once` can miss a hit
there. (`have h : T := calc⏎ …` on one line used to swallow the rest of the block into the calc steps; fixed in
`LeanCalc.insert_newline`, `static/js/parser/lean/tactic.js`.)
2 of 8224 corpus files do not parse at all (text fallbacks run).

AGENTS.md rules now fully checked here (candidates to drop from AGENTS.md, since the warning quotes the rule):
"within the `given` section: propositions come first, expressions come next" (`given-prop-first`).
Still only partially checked: "inline `have` … if it is referenced only once" (`have-inline-once` covers the
"used once, by the very next `exact` / `apply`" case).
