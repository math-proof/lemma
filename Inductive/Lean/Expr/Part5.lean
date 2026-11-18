module

public import Def.Lean.Meta.Expr
public import Def.Lean.Expr.Singleton
public import Def.Lean.Expr.Part9
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


public inductive TreeNode where
  | Operator (op : Operator)
  | const (expr : Expr)


