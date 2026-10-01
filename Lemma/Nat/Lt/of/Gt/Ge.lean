import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h₀ : b > x)
  (h₁ : x ≥ a) :
-- imply
  a < b := by
-- proof
  exact lt_of_le_of_lt h₁ h₀


-- created on 2026-09-27
