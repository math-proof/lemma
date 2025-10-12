import sympy.Basic


@[main]
private lemma main
  {a b : ℕ}
-- given
  (h : a ≥ b) :
-- imply
  a - (a - b) = b :=
-- proof
  Nat.sub_sub_self h


-- created on 2025-06-17
