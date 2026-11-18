module

public meta import Def.Lean.Meta.CtorName
public import Class.Lean.Meta.CtorName
public import Def.Lean.Meta.Expr
public import Def.Lean.Expr.Singleton
public import Def.Lean.Expr

@[expose] public section

open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


structure UnaryPrefix where
  name : Name
deriving BEq, Repr

#eval mkCtorName ``UnaryPrefix
