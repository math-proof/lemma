import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h₀ : a < x)
  (h₁ : b > x) :
-- imply
  a < b := by
-- proof
  exact lt_trans h₀ h₁


-- created on 2019-12-20
