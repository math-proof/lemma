import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a x b : α}
-- given
  (h₀ : a = x)
  (h₁ : x > b) :
-- imply
  a > b := by
-- proof
  rw [h₀]
  exact h₁


-- created on 2026-09-27
