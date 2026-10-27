import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Def.Lean.Expr.Part7
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


instance : ToString Operator where
  toString := Operator.operator


