module

public import Def.Lean.Meta.Expr.Part4
public import Def.Lean.Expr.Singleton.Part2
public import Def.Lean.Expr.Part9
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


public inductive TreeNode where
  | Operator (op : Operator)
  | const (expr : Expr)


