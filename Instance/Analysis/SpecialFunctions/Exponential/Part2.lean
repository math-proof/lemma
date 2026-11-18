module

public import Theorem.Hyperreal.UFn.of.All_UFn
public import Theorem.Int.Abs.eq.Max_Neg
public import Theorem.Analysis.SpecialFunctions.Exponential.Part2
public import Class.Analysis.SpecialFunctions.Exponential.Part2
public import Instance.Analysis.SpecialFunctions.Exponential

@[expose] public section

open Filter Hyperreal Int


noncomputable instance : ExpNeZero ℝ where
  exp_ne_zero := Real.exp_ne_zero

noncomputable instance : ExpNeZero ℂ where
  exp_ne_zero := Complex.exp_ne_zero

noncomputable instance : ExpNeZero ℝ* where
  exp_ne_zero := Hyperreal.exp_ne_zero

