import sympy.Basic


@[main]
private lemma main
  {n b : ℕ}
-- given
  (i : Fin b)
  (h : b ≤ n) :
-- imply
  ↑i < n :=
-- proof
  Fin.val_lt_of_le i h


-- created on 2025-12-31
