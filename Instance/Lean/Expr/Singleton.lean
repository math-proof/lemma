module

public import Def.Lean.Name
public import Mathlib.Basic.Real.Basic
public import Def.Lean.Expr.Singleton

@[expose] public section

open Lean


instance : ToString Constant where
  toString := Constant.toString


