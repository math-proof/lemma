import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


structure Func where
  priority : Nat
  -- lean operator
  operator : String
  -- latex command
  command : String
deriving BEq, Repr, Inhabited


structure BinaryInfix where
  name : Name
deriving BEq, Repr


