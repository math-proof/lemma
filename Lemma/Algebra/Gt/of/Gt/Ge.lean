import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a > b)
  (h₁ : b ≥ c) :
-- imply
  a > c :=
-- proof
  lt_of_lt_of_le' h₀ h₁


-- created on 2024-11-29
