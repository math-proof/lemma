import Lemma.Rat.EqCoeS.is.Eq
open Rat


@[main]
private lemma main
  [DivisionRing R]
  [CharZero R]
  {a b : ℚ}
-- given
  (h : a ≠ b) :
-- imply
  (a : R) ≠ (b : R) := by
-- proof
  contrapose! h
  rwa [EqCoeS.is.Eq] at h


-- created on 2025-12-10
