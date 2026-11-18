module

public import Mathlib.Analysis.Real.Hyperreal
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

open Filter Hyperreal Int


noncomputable def Hyperreal.exp (x : ℝ*) : ℝ* :=
  x.map Real.exp
