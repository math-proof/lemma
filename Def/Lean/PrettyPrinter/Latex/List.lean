module

public import Def.Lean.PrettyPrinter.Latex.Expr.Basic

@[expose] public section

open Lean (Name)
set_option linter.unusedVariables false


/-- `names` with every `fun` / `let` / `∀` binder of `binders` removed (same `rvToken`). -/
def List.withoutLimitBinders (names : List Name) (binders : List Expr) : List Name :=
  let hidden := Expr.limitBinderNames binders
  names.filter fun n => !hidden.any (fun h => rvToken h == rvToken n)
