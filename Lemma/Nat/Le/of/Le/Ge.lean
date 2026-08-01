import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h₀ : a ≤ x)
  (h₁ : b ≥ x) :
-- imply
  a ≤ b := by
-- proof
  apply h₀.trans h₁


-- created on 2018-09-10
