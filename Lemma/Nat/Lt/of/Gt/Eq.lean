import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h₀ : b > x)
  (h₁ : x = a) :
-- imply
  a < b := by
-- proof
  rw [← h₁]
  exact h₀


-- created on 2026-09-27
