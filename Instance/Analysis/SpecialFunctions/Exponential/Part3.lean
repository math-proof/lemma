module

public import Theorem.Hyperreal.UFn.of.All_UFn
public import Theorem.Int.Abs.eq.Max_Neg
public import Theorem.Analysis.SpecialFunctions.Exponential
public import Theorem.Analysis.SpecialFunctions.Exponential.Part2
public import Class.Analysis.SpecialFunctions.Exponential.Part3
public import Instance.Analysis.SpecialFunctions.Exponential
public import Instance.Analysis.SpecialFunctions.Exponential.Part2

@[expose] public section

open Filter Hyperreal Int


noncomputable instance : ExpPos ℝ where
  exp_pos := Real.exp_pos
  exp_eq_exp := Real.exp_eq_exp
  exp_lt_exp := Real.exp_lt_exp

noncomputable instance : ExpPos ℝ* where
  exp_pos := Hyperreal.exp_pos
  exp_eq_exp := Hyperreal.exp_eq_exp
  exp_lt_exp := Hyperreal.exp_strictMono.lt_iff_lt

