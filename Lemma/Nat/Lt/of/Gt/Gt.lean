import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h₀ : b > x)
  (h₁ : x > a) :
-- imply
  a < b := by
-- proof
  exact lt_trans h₁ h₀


-- created on 2019-07-20
