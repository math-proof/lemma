import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Def.Lean.Expr.Part8
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


inductive Expr where

  | nil

  | const (val : Constant)

  | sort (u : Level)

  | Symbol (name : Name) (type : Expr)

  | Basic (func : Operator) (args : List Expr) (level : Nat)

  | Binder (binder : Binder) (binderName : Name) (binderType : Expr) (value : Expr)
deriving Inhabited, BEq, CtorName

