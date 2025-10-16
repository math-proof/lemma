import Lemma.Algebra.Floor.gt.Sub_1
import Lemma.Algebra.GtSubS.of.Gt
import Lemma.Algebra.Gt.of.Gt.Gt
import Lemma.Nat.Ge_Add_1.of.Gt
open Algebra Nat


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
  have h := GtSubS.of.Gt h 1
  have h := Gt.of.Gt.Gt this h
  norm_cast at h
  have h := Ge_Add_1.of.Gt h
  linarith


-- created on 2025-10-01
