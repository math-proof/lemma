import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a x b : α}
-- given
  (h₀ : a = x)
  (h₁ : x ≤ b) :
-- imply
  a ≤ b := by
-- proof
  rw [h₀]
  exact h₁


@[main]
private lemma subst
  {y x k b t : ℝ}
-- given
  (h₀ : y = x * k + b)
  (h₁ : x ≤ t)
  (h₂ : k > 0) :
-- imply
  y ≤ t * k + b := by
-- proof
  have := mul_le_mul_of_nonneg_right h₁ h₂.le
  rw [h₀]
  linarith


-- created on 2026-09-27
