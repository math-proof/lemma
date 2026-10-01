import sympy.sets.sets
import sympy.Basic


@[main]
private lemma quadratic
  {x m M a b c : ℝ}
-- given
  (ha : a > 0)
  (h₀ : x < M)
  (h₁ : x > m) :
-- imply
  a * x * x + b * x + c < max (a * m * m + b * m + c) (a * M * M + b * M + c) := by
-- proof
  by_contra hc
  have h₂ := not_lt.mp hc
  have e₁ : a * m * m + b * m + c ≤ a * x * x + b * x + c := le_trans (le_max_left _ _) h₂
  have e₂ : a * M * M + b * M + c ≤ a * x * x + b * x + c := le_trans (le_max_right _ _) h₂
  nlinarith [mul_nonneg (sub_nonneg.mpr e₁) (sub_pos.mpr h₀).le, mul_nonneg (sub_nonneg.mpr e₂) (sub_pos.mpr h₁).le,
    mul_pos (mul_pos (mul_pos ha (sub_pos.mpr h₀)) (sub_pos.mpr h₁)) (sub_pos.mpr (lt_trans h₁ h₀))]


-- created on 2019-12-19
