import sympy.Basic


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
-- given
  (a b : ℚ) :
-- imply
  (a : R) < (b : R) ↔ a < b :=
-- proof
  Rat.cast_lt


-- created on 2025-10-16
