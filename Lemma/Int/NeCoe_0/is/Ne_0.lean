import sympy.Basic


@[main, mp, mpr]
private lemma main
  [AddGroupWithOne α]
  [CharZero α]
  {n : ℤ} :
-- imply
  (n : α) ≠ 0 ↔ n ≠ 0 :=
-- proof
  Int.cast_ne_zero


-- created on 2025-08-02
-- updated on 2025-10-16
