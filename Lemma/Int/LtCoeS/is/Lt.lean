import sympy.Basic


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
-- given
  (a b : ℤ) :
-- imply
  (a : R) < (b : R) ↔ a < b :=
-- proof
  Int.cast_lt


-- created on 2025-10-16
