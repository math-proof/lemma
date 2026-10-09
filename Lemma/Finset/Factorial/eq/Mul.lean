import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
-- given
  (h : n > 0) :
-- imply
  Nat.factorial n = n * Nat.factorial (n - 1) :=
-- proof
  (Nat.mul_factorial_pred (by omega)).symm


-- created on 2020-08-06
