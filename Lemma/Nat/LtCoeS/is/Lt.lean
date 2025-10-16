import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
-- given
  (a b : ℕ) :
-- imply
  (a : R) < (b : R) ↔ a < b :=
-- proof
  Nat.cast_lt


-- created on 2025-03-29
-- updated on 2025-10-16
