import sympy.Basic


@[main, comm]
private lemma main
  {z : ℤ}
-- given
  (h : z ≥ 0) :
-- imply
  z.toNat = z :=
-- proof
  Int.toNat_of_nonneg h


-- created on 2025-06-07
