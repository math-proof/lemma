import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddGroupWithOne R]
  [CharZero R]
  {a b : ℤ} :
-- imply
  (a : R) = (b : R) ↔ a = b :=
-- proof
  Int.cast_inj


-- created on 2025-10-08
