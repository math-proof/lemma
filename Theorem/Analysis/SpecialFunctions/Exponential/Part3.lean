module

public import Theorem.Hyperreal.UFn.of.All_UFn
public import Theorem.Int.Abs.eq.Max_Neg
public import Instance.Analysis.SpecialFunctions.Exponential
public section

open Filter Hyperreal Int


@[simp]
theorem Hyperreal.exp.rfl (x : ℝ*) : Exp.exp x = x.exp := by rfl

