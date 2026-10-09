import Mathlib.Analysis.Complex.Trigonometric
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  (Real.cos x : ℂ) = Complex.cosh (x * Complex.I) := by
-- proof
  rw [Complex.cosh_mul_I, Complex.ofReal_cos x]


-- created on 2023-11-26
