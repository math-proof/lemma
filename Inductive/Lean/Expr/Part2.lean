module

public import Def.Lean.Meta.Expr.Part4
public import Def.Lean.Expr.Singleton.Part2
public import Def.Lean.Expr.Part5
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


public inductive ExprWithAttr where
  | Lean_function (name : Name)
  | Lean_operatorname (name : Name)
  | Lean_typeclass (name : Name)
  | LeanLemma (name : Name)
  | LeanMethod (name : Name) (idx : Nat) --idx denotes the first index of the self parameter in the default argument list
  | LeanProperty (name : Name)
deriving BEq, Repr


