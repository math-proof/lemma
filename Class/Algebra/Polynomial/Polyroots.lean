module

public import Theorem.Algebra.Power.Part2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Hyperreal


public section

class Root (α : Type _) where
  sqrt : α → α
  cubic : α → α
  quartic : α → α


