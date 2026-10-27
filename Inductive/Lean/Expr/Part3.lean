import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Def.Lean.Expr.Part6
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


inductive Operator where
  | BinaryInfix (op : BinaryInfix)
  | UnaryPrefix (op : UnaryPrefix)
  | UnaryPostfix (op : UnaryPostfix)
  | ExprWithLimits (op : ExprWithLimits)
  | Special (op : Special)
  | ExprWithAttr (op : ExprWithAttr)
deriving BEq, CtorName, Repr


