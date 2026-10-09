import sympy.Basic


@[path]
private lemma main
  [Preorder α]
  {a x b : α}
-- given
  (h₀ : b > x)
  (h₁ : a ≤ x) :
-- imply
  b > a :=
-- proof
  lt_of_le_of_lt h₁ h₀


@[path]
private lemma subst
  {y x k b t : ℝ}
-- given
  (h₀ : x * k + b > y)
  (h₁ : x ≤ t)
  (h₂ : k > 0) :
-- imply
  t * k + b > y := by
-- proof
  have := mul_le_mul_of_nonneg_right h₁ h₂.le
  linarith


-- created on 2019-07-30
