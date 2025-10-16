import Lemma.Int.LeCoeS.is.Le
open Int


@[main, comm, mp, mpr]
private lemma main
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
-- given
  (a b : ℤ) :
-- imply
  (a : R) ≥ (b : R) ↔ a ≥ b := by
-- proof
  apply LeCoeS.is.Le


-- created on 2025-10-16
