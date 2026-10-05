import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/--
Textbook sum over the *value* of a bound sequence at a fixed index.  In probability texts one writes
`∑_{y_t} P(… y_t = y_t …)` for the sum over the states of the single coordinate `y_t`; here

* `∑ «y.bvar» t, body` is the plain finite sum `∑ c, body'` (over `Finset.univ` of the state type,
  which is inferred from `body` and needs `[Fintype _]`), where `body'` is `body` with every
  application `«y.bvar» t` replaced by the bound variable `c`.

It is purely syntactic (a macro): the argument `t` may be any term, and an application is replaced when
its single argument is syntactically equal to `t`.  Other occurrences of `«y.bvar»` (e.g.
`«y.bvar» (t + 1)`, or a bare `«y.bvar»`) are left alone and are then unbound-variable errors.
The sum is *not* over functions `ℕ → Y`.

The body is parsed at precedence 67 (like Mathlib's `∑`).  The syntax has high priority so that
`∑ a t, f` is read by this macro instead of as the nested sum `∑ a, ∑ t, f`; when the body contains no
`a t`, the macro expands to exactly that nested sum when `t` is an identifier, so Mathlib's
`∑ i j, f` keeps its meaning.  `∑ x, f`, `∑ x ∈ s, f`, `∑ x : T, f` are not affected.
-/
syntax:67 (name := sumAt) (priority := high) "∑ " ident term:max ", " term:67 : term

open Lean in
macro_rules
  | `(∑ $x:ident $t, $body) => do
    let c := mkIdent (← Macro.addMacroScope `c)
    let rec go (s : Syntax) : StateM Bool Syntax := do
      match s with
      | .node info kind args =>
        if kind == ``Lean.Parser.Term.app && args.size == 2 && args[0]!.isIdent
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
    else if t.raw.isIdent then
      `(∑ $x:ident, ∑ $(⟨t.raw⟩):ident, $body)
    else
      Macro.throwError s!"'∑ {x.getId} _, …': the body does not contain the application '{x.getId} _' of the bound sequence to the given index"

-- created on 2026-10-05
