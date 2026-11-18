module

public import Def.Lean.Meta.Expr
public import Def.Lean.Expr.Singleton
public import Def.Lean.Expr.Operator

@[expose] public section

open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


instance : ToString Operator where
  toString := Operator.operator
