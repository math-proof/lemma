import Lemma.Nat.LtCoeS.is.Lt
open Nat


@[main, comm, mp, mpr]
private lemma main
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
-- given
  (a b : ℕ) :
-- imply
  (a : R) > (b : R) ↔ a > b := by
-- proof
  apply LtCoeS.is.Lt


-- created on 2025-03-29
-- updated on 2025-10-16
