import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  (Real.sin x : ℂ) = (Complex.exp (Complex.I * x) - Complex.exp (-Complex.I * x)) / (2 * Complex.I) := by
-- proof
  rw [Complex.ofReal_sin, Complex.sin, eq_div_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
  ring_nf
  rw [Complex.I_sq]
  ring


-- created on 2018-06-15
