import sympy.Basic


@[main]
private lemma quadratic
  {x m M a b c : ℝ}
-- given
  (h₀ : x ≥ m)
  (h₁ : x ≤ M)
  (h₂ : a > 0) :
-- imply
  a * x * x + b * x + c ≤ max (a * m * m + b * m + c) (a * M * M + b * M + c) := by
-- proof
  rcases le_total (a * (x + m) + b) 0 with hc | hc
  ·
    exact le_max_of_le_left (by nlinarith [mul_nonneg (sub_nonneg.mpr h₀) (neg_nonneg.mpr hc)])
  ·
    have hc' : a * (x + M) + b ≥ 0 := by nlinarith
    exact le_max_of_le_right (by nlinarith [mul_nonneg (sub_nonneg.mpr h₁) hc'])


-- created on 2026-09-27
