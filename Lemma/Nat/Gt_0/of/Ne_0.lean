import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : n ≠ 0) :
-- imply
  n > 0 := 
-- proof
  Nat.pos_of_ne_zero h


-- created on 2024-07-01
-- updated on 2025-10-13
