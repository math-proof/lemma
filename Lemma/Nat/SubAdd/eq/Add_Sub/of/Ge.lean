import sympy.Basic


@[main, comm]
private lemma main
  {b c : ℕ}
-- given
  (h : b ≥ c)
  (a : ℕ):
-- imply
  a + b - c = a + (b - c) :=
-- proof
  Nat.add_sub_assoc h a


-- created on 2025-03-31
-- updated on 2025-06-08
