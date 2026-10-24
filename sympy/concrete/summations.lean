import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/--
Textbook sum over the *value* of a bound sequence at a fixed index.  In probability texts one writes
`∑_{y_t} P(… y_t = y_t …)` for the sum over the states of the single coordinate `y_t`; here

* `∑ «y.bvar»[t], body` (preferred) is the plain finite sum `∑ c, body'` (over `Finset.univ` of the
  state type, inferred from `body` and needing `[Fintype _]`), where `body'` is `body` with every
  `«y.bvar»[t]` (Fun / `GetElem`) or application `«y.bvar» t` replaced by the bound variable `c`.
* `∑ «y.bvar» t, body` is the same macro with juxtaposition instead of brackets (kept for older lemmas).

It is purely syntactic: the index `t` may be any term, and an occurrence is replaced when its index /
single argument is syntactically equal to `t`.  Other occurrences of `«y.bvar»` (e.g.
`«y.bvar»[t + 1]`, `«y.bvar» (t + 1)`, or a bare `«y.bvar»`) are left alone and are then
unbound-variable errors.  The sum is *not* over functions `ℕ → Y` / `ℕ ⇀ Y`.

The body is parsed at precedence 67 (like Mathlib's `∑`).  Both syntaxes have high priority so that
`∑ a[t], f` / `∑ a t, f` are read by this macro instead of as nested sums; when the body contains no
matching occurrence at index `t`, the juxtaposition form falls back to Mathlib's `∑ a, ∑ t, f` when
`t` is an identifier.  `∑ x, f`, `∑ x ∈ s, f`, `∑ x : T, f` are not affected.
-/
syntax:67 (name := sumAtGetElem) (priority := high)
  "∑ " ident noWs "[" withoutPosition(term) "]" ", " term:67 : term

syntax:67 (name := sumAt) (priority := high)
  "∑ " ident term:max ", " term:67 : term

open Lean in
/-- Shared expansion: replace `x[t]` / `x t` in `body` by a fresh `c`, else fall back when allowed. -/
def expandSumAt (x : TSyntax `ident) (t : Term) (body : Term) (allowNestedFallback : Bool) :
    MacroM Term := do
  let c := mkIdent (← Macro.addMacroScope `c)
  let rec go (s : Syntax) : StateM Bool Syntax := do
    match s with
    | .node info kind args =>
      if kind == ``«term__[_]» && args.size == 4 && args[0]!.isIdent
          && args[0]!.getId == x.getId && args[2]!.structEq t.raw then
        set true
        return c.raw
      else if kind == ``Lean.Parser.Term.app && args.size == 2 && args[0]!.isIdent
          && args[0]!.getId == x.getId && args[1]!.getNumArgs == 1
          && args[1]![0]!.structEq t.raw then
        set true
        return c.raw
      else
        return .node info kind (← args.mapM go)
    | s => return s
  let (body', found) := (go body.raw).run false
  if found then
    `(∑ $c:ident, $(⟨body'⟩))
  else if allowNestedFallback && t.raw.isIdent then
    `(∑ $x:ident, ∑ $(⟨t.raw⟩):ident, $body)
  else
    Macro.throwError s!"'∑ {x.getId}[_], …': the body does not contain '{x.getId}[_]' / '{x.getId} _' at the given index"

open Lean in
macro_rules (kind := sumAtGetElem)
  | `(∑ $x:ident[$t], $body) => expandSumAt x t body false

open Lean in
macro_rules (kind := sumAt)
  | `(∑ $x:ident $t, $body) => expandSumAt x t body true

-- created on 2026-10-05
-- updated on 2026-10-22
