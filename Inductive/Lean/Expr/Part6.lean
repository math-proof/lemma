import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Def.Lean.Expr.Part10
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


/-- Direction of `lim [x → …]`. -/
inductive LimTo where
  | inf
  | ninf
  | nhds (x : Expr)
  | nhdsPos (x : Expr)
  | nhdsNeg (x : Expr)
deriving BEq

