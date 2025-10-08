import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [DivisionRing R]
  [CharZero R]
  {a b : ℚ} :
-- imply
  (a : R) = (b : R) ↔ a = b :=
-- proof
  Rat.cast_inj


-- created on 2025-10-08
