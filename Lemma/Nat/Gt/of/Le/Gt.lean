import sympy.Basic


@[path]
private lemma main
  [Preorder α]
  {a x b : α}
-- given
  (h₀ : a ≤ x)
  (h₁ : b > x) :
-- imply
  b > a :=
-- proof
  lt_of_le_of_lt h₀ h₁


-- created on 2019-07-29
