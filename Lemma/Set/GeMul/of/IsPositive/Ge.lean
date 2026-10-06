import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {g h : ℝ → ℝ}
-- given
  (h₀ : 0 < x)
  (h₁ : h x ≤ g x) :
-- imply
  h x * x ≤ g x * x := by
-- proof
  exact mul_le_mul_of_nonneg_right h₁ h₀.le


-- created on 2023-10-15
