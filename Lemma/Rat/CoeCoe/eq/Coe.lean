import sympy.Basic


@[main, comm]
private lemma main
  [DivisionRing R]
-- given
  (n : ℕ) :
-- imply
  ((n : ℚ) : R) = n :=
-- proof
  Rat.cast_natCast n


-- created on 2025-10-14
