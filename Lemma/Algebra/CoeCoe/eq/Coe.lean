import sympy.Basic


@[main, comm]
private lemma int
  [AddGroupWithOne R]
-- given
  (n : ℕ) :
-- imply
  ((n : ℤ) : R) = n :=
-- proof
  Int.cast_natCast n


@[main, comm]
private lemma main
  [DivisionRing R]
-- given
  (n : ℕ) :
-- imply
  ((n : ℚ) : R) = n :=
-- proof
  Rat.cast_natCast n


-- created on 2025-09-30
