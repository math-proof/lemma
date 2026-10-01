import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h₀ : b ≥ x)
  (h₁ : a < x) :
-- imply
  a < b := by
-- proof
  exact lt_of_lt_of_le h₁ h₀


-- created on 2019-08-02
