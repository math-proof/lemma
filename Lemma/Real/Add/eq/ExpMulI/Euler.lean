import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Complex.cos x - Complex.I * Complex.sin x = Complex.exp (-Complex.I * x) := by
-- proof
  rw [show -Complex.I * x = (-x : ℂ) * Complex.I by ring, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring


-- created on 2022-01-20
