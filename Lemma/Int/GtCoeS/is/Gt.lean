import Lemma.Int.LtCoeS.is.Lt
open Int


@[main, comm, mp, mpr]
private lemma main
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
-- given
  (a b : ℤ) :
-- imply
  (a : R) > (b : R) ↔ a > b := by
-- proof
  apply LtCoeS.is.Lt


-- created on 2025-10-16
