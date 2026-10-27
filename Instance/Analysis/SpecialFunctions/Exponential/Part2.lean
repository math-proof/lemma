import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Int.Abs.eq.Max_Neg
import Class.Analysis.SpecialFunctions.Exponential.Part2
open Filter Hyperreal Int


noncomputable instance : ExpNeZero ℝ where
  exp_ne_zero := Real.exp_ne_zero

noncomputable instance : ExpNeZero ℂ where
  exp_ne_zero := Complex.exp_ne_zero

noncomputable instance : ExpNeZero ℝ* where
  exp_ne_zero := Hyperreal.exp_ne_zero

