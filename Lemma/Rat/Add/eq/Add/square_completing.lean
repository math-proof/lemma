import Mathlib.Data.Complex.Basic
import sympy.Basic


@[main]
private lemma main
  {a x b c : ℂ}
  -- given
  (ha : a ≠ 0)
  -- imply
  : a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 + (4 * a * c - b ^ 2) / (4 * a) := by
  -- proof
  have h2 : (2 * a : ℂ) ≠ 0 := by
    intro h
    apply ha
    simpa [mul_eq_zero] using h
  have h4 : (4 * a : ℂ) ≠ 0 := by
    intro h
    apply ha
    simpa [mul_eq_zero] using h
  field_simp [ha, h2, h4]
  <;> ring

-- created on 2023-04-10
