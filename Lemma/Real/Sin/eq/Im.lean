import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.sin x = (Complex.exp (Complex.I * x)).im := by
-- proof
  rw [← Complex.exp_ofReal_mul_I_im x, mul_comm]


-- created on 2023-06-03
