module

public import Theorem.Hyperreal.UFn.of.All_UFn
public import Theorem.Int.Abs.eq.Max_Neg
public import Theorem.Analysis.SpecialFunctions.Exponential
public import Theorem.Analysis.SpecialFunctions.Exponential.Part2
public import Class.Analysis.SpecialFunctions.Exponential

@[expose] public section

open Filter Hyperreal Int


noncomputable instance : Exp ℝ where
  exp := Real.exp
  exp_add := Real.exp_add
  exp_zero := Real.exp_zero
  exp_neg := Real.exp_neg

noncomputable instance : Exp ℂ where
  exp := Complex.exp
  exp_add := Complex.exp_add
  exp_zero := Complex.exp_zero
  exp_neg := Complex.exp_neg

noncomputable instance : Exp ℝ* where
  exp := Hyperreal.exp
  exp_add := Hyperreal.exp_add
  exp_zero := Hyperreal.exp_zero
  exp_neg := Hyperreal.exp_neg

noncomputable instance : ExpNeZero ℝ where
  exp_ne_zero := Real.exp_ne_zero

noncomputable instance : ExpNeZero ℂ where
  exp_ne_zero := Complex.exp_ne_zero

noncomputable instance : ExpNeZero ℝ* where
  exp_ne_zero := Hyperreal.exp_ne_zero

noncomputable instance : ExpPos ℝ where
  exp_pos := Real.exp_pos
  exp_eq_exp := Real.exp_eq_exp
  exp_lt_exp := Real.exp_lt_exp

noncomputable instance : ExpPos ℝ* where
  exp_pos := Hyperreal.exp_pos
  exp_eq_exp := Hyperreal.exp_eq_exp
  exp_lt_exp := Hyperreal.exp_strictMono.lt_iff_lt
