import sympy.Basic


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h : x > y) :
-- imply
  x ≥ y + 1 := by
-- proof
  exact Nat.succ_le_of_lt h


-- created on 2026-10-03
