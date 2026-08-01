import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : b < c) :
-- imply
  a < c :=
-- proof
  lt_of_le_of_lt h₀ h₁


-- created on 2018-02-27
-- updated on 2025-04-04
