import Lemma.Rat.LeCoeS.is.Le
open Rat


@[main, comm, mp, mpr]
private lemma main
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
-- given
  (a b : ℚ) :
-- imply
  (a : R) ≥ (b : R) ↔ a ≥ b := by
-- proof
  apply LeCoeS.is.Le


-- created on 2025-10-16
