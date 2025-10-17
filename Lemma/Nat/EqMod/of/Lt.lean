import sympy.Basic


@[main]
private lemma main
  {k n : ℕ}
-- given
  (h : k < n) :
-- imply
  k % n = k :=
-- proof
  Nat.mod_eq_of_lt h


-- created on 2025-06-02
