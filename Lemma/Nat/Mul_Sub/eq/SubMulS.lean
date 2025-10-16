import sympy.Basic


@[main, comm]
private lemma main
-- given
  (x a b : ℕ) :
-- imply
  x * (a - b) = x * a - x * b :=
-- proof
  Nat.mul_sub x a b


-- created on 2025-10-16
