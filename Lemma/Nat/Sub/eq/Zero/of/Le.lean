import sympy.Basic


@[main]
private lemma main
-- given
  (h : a ≤ b) :
-- imply
  a - b = 0 :=
-- proof
  Nat.sub_eq_zero_of_le h


-- created on 2025-05-04
