import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a x b : α}
-- given
  (h₀ : a = x)
  (h₁ : x < b) :
-- imply
  a < b := by
-- proof
  rw [h₀]
  exact h₁


@[main]
private lemma subst
  {y b x t k : ℝ}
-- given
  (h₀ : y = x * k + b)
  (h₁ : x < t)
  (h₂ : k > 0) :
-- imply
  y < t * k + b := by
-- proof
  rw [h₀]
  nlinarith


-- created on 2023-05-01
