import sympy.Basic


@[main, comm]
private lemma main
  [Monoid M]
-- given
  (a : M)
  (m n : ℕ) :
-- imply
  a ^ (m + n) = a ^ m * a ^ n :=
-- proof
  pow_add a m n


-- created on 2025-03-15
