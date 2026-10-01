import sympy.Basic


@[main]
private lemma main
  {n k : ℕ}
-- given
  (h : k ≤ n) :
-- imply
  n.choose k = n.choose (n - k) :=
-- proof
  (Nat.choose_symm h).symm


-- created on 2026-09-27
