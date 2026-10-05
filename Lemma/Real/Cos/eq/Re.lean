import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  Real.cos x = (Complex.exp (Complex.I * x)).re := by
-- proof
  rw [← Complex.exp_ofReal_mul_I_re x, mul_comm]


-- created on 2023-06-03
