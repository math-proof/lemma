import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Instance.Lean.Expr
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


def Operator.command : Operator → String :=
  Func.command ∘ Operator.func

def Operator.methodIdx : Operator → Nat
  | ExprWithAttr (.LeanMethod _ idx) => idx
  | _ => 0


