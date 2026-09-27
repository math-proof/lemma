import sympy.Basic


@[main]
private lemma main
  {p x y : ℝ}
-- given
  (h₀ : p ≤ 1)
  (h₁ : y ≤ x) :
-- imply
  p * x + (1 - p) * y ≤ x := by
-- proof
  nlinarith [mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr h₀)]


-- created on 2026-09-26
