import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Structure.Lean.Expr.Part3
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


def UnaryPostfix.func: UnaryPostfix → Func
  | ⟨name⟩ =>
    match name with
    | `Inv.inv => ⟨2048, "⁻¹", "^{-1}"⟩  -- https://github.com/leanprover/lean4/blob/v4.23.0/src/Init/Notation.lean#L295
    | _ => panic! s!"UnaryPostfix.func : unknown operator {name}"


