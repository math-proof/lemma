import Def.Lean.Meta.Expr.Part4
import Def.Lean.Expr.Singleton.Part2
import Def.Lean.Expr
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


structure UnaryPrefix where
  name : Name
deriving BEq, CtorName, Repr


