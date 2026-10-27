import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Def.Lean.Expr.Part2
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


structure UnaryPostfix where
  name : Name
deriving BEq, Repr


