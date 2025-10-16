import sympy.Basic


@[main, mp, mpr]
private lemma main
  [AddMonoidWithOne α]
  [CharZero α]
  {n : ℕ} :
-- imply
  (n : α) ≠ 0 ↔ n ≠ 0 :=
-- proof
  Nat.cast_ne_zero


-- created on 2025-10-16
