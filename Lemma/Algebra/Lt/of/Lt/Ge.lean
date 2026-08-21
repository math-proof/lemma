import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h₀ : a < x)
  (h₁ : b ≥ x) :
-- imply
  a < b :=
-- proof
  lt_of_lt_of_le h₀ h₁


-- created on 2018-11-04
-- updated on 2026-08-20
