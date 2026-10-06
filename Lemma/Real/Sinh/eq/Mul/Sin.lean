import Mathlib.Analysis.Complex.Trigonometric
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℂ) :
-- imply
  Complex.sinh x = -Complex.I * Complex.sin (x * Complex.I) := by
-- proof
  calc
    Complex.sinh x
      = Complex.sinh x * (-(Complex.I * Complex.I)) := by rw [Complex.I_mul_I]; ring
    _ = -Complex.I * (Complex.sinh x * Complex.I) := by ring
    _ = -Complex.I * Complex.sin (x * Complex.I) := by rw [Complex.sin_mul_I]


-- created on 2023-11-26
