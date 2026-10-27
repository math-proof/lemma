import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Int.Abs.eq.Max_Neg
import Class.Analysis.SpecialFunctions.Exponential.Part3
open Filter Hyperreal Int


noncomputable instance : ExpPos ℝ where
  exp_pos := Real.exp_pos
  exp_eq_exp := Real.exp_eq_exp
  exp_lt_exp := Real.exp_lt_exp

noncomputable instance : ExpPos ℝ* where
  exp_pos := Hyperreal.exp_pos
  exp_eq_exp := Hyperreal.exp_eq_exp
  exp_lt_exp := Hyperreal.exp_strictMono.lt_iff_lt

