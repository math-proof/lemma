import Def.Lean.Meta.Expr.Part4
import Def.Lean.Expr.Singleton.Part2
import Def.Lean.Expr.Part7
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


instance : ToString Operator where
  toString := Operator.operator


