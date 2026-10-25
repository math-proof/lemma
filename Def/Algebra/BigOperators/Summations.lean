import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Syntax.Algebra.BigOperators.Summations


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

