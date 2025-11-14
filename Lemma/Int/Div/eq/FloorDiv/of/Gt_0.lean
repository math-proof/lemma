import Lemma.Int.Div.eq.AddDiv___Mod
import Lemma.Int.Div.lt.One.of.Gt_0
import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Int.GeDivS.of.Gt_0
open Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  n / d = ⌊n / (d : α)⌋ := by
-- proof
  apply Eq.symm
  rw [EqFloor.is.Le.Lt]
  constructor
  ·
    exact GeDivS.of.Gt_0 h
  ·
    simp [Div.eq.AddDiv___Mod n]
    exact Div.lt.One.of.Gt_0 h


-- created on 2025-10-08
-- updated on 2025-11-14
