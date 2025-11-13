import Lemma.Rat.Floor.gt.Sub_1
import Lemma.Int.LtSubS.is.Lt
import Lemma.Nat.Gt.of.Gt.Gt
import Lemma.Nat.LeAdd_1.of.Lt
open Nat Int Rat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
  {y : ℤ}
-- given
  (h : x > y) :
-- imply
  ⌊x⌋ ≥ y := by
-- proof
  have := Floor.gt.Sub_1 x
  have h := GtSubS.of.Gt 1 h
  have h := Gt.of.Gt.Gt this h
  norm_cast at h
  have h := Ge_Add_1.of.Gt h
  linarith


-- created on 2025-10-01
