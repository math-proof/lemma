import sympy.Basic


@[main]
private lemma main
  {x a : ℕ}
-- given
  (h : x ≤ a) :
-- imply
  x < a + 1 := by
-- proof
  exact Nat.lt_succ_of_le h


-- created on 2021-02-17
