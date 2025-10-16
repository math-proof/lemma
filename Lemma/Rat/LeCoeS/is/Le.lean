import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
-- given
  (a b : ℚ) :
-- imply
  (a : R) ≤ (b : R) ↔ a ≤ b :=
-- proof
  Rat.cast_le


-- created on 2025-10-16
