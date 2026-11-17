module

public import Def.Lean.Meta.Expr.Part4
public import Def.Lean.Expr.Singleton.Part2
public import Def.Lean.Expr.Part4
public section

open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


structure Special where
  name : Name
deriving BEq, Repr


