module

public import Def.Lean.Name
public import Mathlib.Basic.Real.Basic
open Lean


public inductive Constant where
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


