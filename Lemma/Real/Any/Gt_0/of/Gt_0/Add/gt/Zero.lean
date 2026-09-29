import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : a > 0)
  (_h₁ : b ^ 2 - 4 * a * c > 0) :
-- imply
  ∃ x, a * x ^ 2 + b * x + c > 0 := by
-- proof
  have ha : a ≠ 0 := by linarith
  have hq : 0 ≤ (|b| + |c| + 1) / a := div_nonneg (by positivity) (by linarith)
  have e : a * ((|b| + |c| + 1) / a) = |b| + |c| + 1 := by field_simp
  refine ⟨1 + (|b| + |c| + 1) / a, ?_⟩
  set X := 1 + (|b| + |c| + 1) / a with hXdef
  have hX1 : 1 ≤ X := by linarith
  have hX2 : a * X ≥ |b| + |c| + 1 := by rw [hXdef, mul_add, e]; linarith
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ X) (sub_nonneg.mpr hX2), mul_le_mul_of_nonneg_right (neg_abs_le b) (by linarith : (0 : ℝ) ≤ X),
    mul_nonneg (sub_nonneg.mpr hX1) (by positivity : (0 : ℝ) ≤ |c| + 1), neg_abs_le c]


-- created on 2026-09-27
