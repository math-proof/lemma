module

public import Def.Lean.Meta.Expr.Part4
public import Def.Lean.Expr.Singleton.Part2
public import Def.Lean.Expr.Part10
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


/-- Direction of `lim[x → …]`. -/
public inductive LimTo where
  | inf
  | ninf
  | nhds (x : Expr)
  | nhdsPos (x : Expr)
  | nhdsNeg (x : Expr)
deriving BEq

