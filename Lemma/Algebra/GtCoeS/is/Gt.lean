import Lemma.Algebra.LtCoeS.is.Lt
open Algebra


@[main, comm, mp, mpr]
private lemma nat
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
-- given
  (a b : ℕ) :
-- imply
  (a : R) > (b : R) ↔ a > b := by
-- proof
  apply LtCoeS.is.Lt.nat


@[main, comm, mp, mpr]
private lemma int
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
-- given
  (a b : ℤ) :
-- imply
  (a : R) > (b : R) ↔ a > b := by
-- proof
  apply LtCoeS.is.Lt.int


@[main, comm, mp, mpr]
private lemma main
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
-- given
  (a b : ℚ) :
-- imply
  (a : R) > (b : R) ↔ a > b := by
-- proof
  apply LtCoeS.is.Lt


-- created on 2025-03-29
-- updated on 2025-04-26
