module

public import Def.Lean.Meta.Expr
public import Def.Lean.Expr.Singleton
public import Def.Lean.Expr.Part4
public section

open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


structure Special where
  name : Name
deriving BEq, Repr


