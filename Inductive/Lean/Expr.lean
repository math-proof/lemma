import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Def.Lean.Expr.Part3
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


inductive ExprWithLimits where
  | Lean_sum
  | Lean_tsum
  | Lean_prod
  | Lean_int (name : Name)
  | Lean_bigcap
  | Lean_bigcup
  | Lean_lim
  | Lean_sup (name : Name)
  | Lean_inf (name : Name)
  | Lean_max (name : Name)
  | Lean_min (name : Name)
  | Lean_forall
  | Lean_exists
  | Lean_lambda
  | Lean_let
deriving BEq, Repr


