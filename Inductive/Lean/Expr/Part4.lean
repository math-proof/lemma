module

public meta import Def.Lean.Meta.CtorName
public import Class.Lean.Meta.CtorName
public import Def.Lean.Meta.Expr
public import Def.Lean.Expr.Singleton
public import Def.Lean.Expr.Operator
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false

@[expose] public section

public inductive Expr where

  | nil

  | const (val : Constant)

  | sort (u : Level)

  | Symbol (name : Name) (type : Expr)

  | Basic (func : Operator) (args : List Expr) (level : Nat)

  | Binder (binder : Binder) (binderName : Name) (binderType : Expr) (value : Expr)
deriving Inhabited, BEq

#eval mkCtorName ``Expr

