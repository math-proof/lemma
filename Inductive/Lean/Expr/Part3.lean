module

public meta import Def.Lean.Meta.CtorName
public import Class.Lean.Meta.CtorName
public import Def.Lean.Meta.Expr.Part4
public import Def.Lean.Expr.Singleton.Part2
public import Def.Lean.Expr.Part6
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false

@[expose] public section

public inductive Operator where
  | BinaryInfix (op : BinaryInfix)
  | UnaryPrefix (op : UnaryPrefix)
  | UnaryPostfix (op : UnaryPostfix)
  | ExprWithLimits (op : ExprWithLimits)
  | Special (op : Special)
  | ExprWithAttr (op : ExprWithAttr)
deriving BEq, Repr

#eval mkCtorName ``Operator


