import Mathlib.Analysis.Complex.Trigonometric
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  (Real.cosh x : ℂ) = Complex.cos (x * Complex.I) := by
-- proof
  rw [Complex.ofReal_cosh, ← Complex.cos_mul_I]


-- created on 2023-11-26
