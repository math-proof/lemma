import Def.Lean.Name
import Mathlib.Basic.Real.Basic
open Lean


inductive Constant where
  | True
  | False
  | NaN
  | EmptySet
  | UniversalSet
  | Pi
  | ImaginaryUnit
  | Nat
  | Int
  | Rat
  | Real
  | Complex
  | true
  | false
  | natVal (val : Nat)
  | ident (name : Name)
  deriving Repr, BEq, Inhabited


