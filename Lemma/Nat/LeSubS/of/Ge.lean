import sympy.Basic


@[main]
private lemma main
  {a b : ℕ}
-- given
  (h : a ≥ b)
  (c : ℕ) :
-- imply
  c - a ≤ c - b :=
-- proof
  Nat.sub_le_sub_left h c


-- created on 2025-06-19
-- updated on 2025-10-16
