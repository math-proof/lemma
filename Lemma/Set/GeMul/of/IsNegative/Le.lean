import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {g h : ℝ → ℝ}
-- given
  (h₀ : x < 0)
  (h₁ : g x ≤ h x) :
-- imply
  h x * x ≤ g x * x := by
-- proof
  exact mul_le_mul_of_nonpos_right h₁ h₀.le


-- created on 2023-10-15
