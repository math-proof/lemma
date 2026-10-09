import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  (Real.sin x : ℂ) = -Complex.I * Complex.sinh (x * Complex.I) := by
-- proof
  rw [Complex.sinh_mul_I, Complex.ofReal_sin]
  ring_nf
  rw [Complex.I_sq]
  ring


-- created on 2023-11-26
