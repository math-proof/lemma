import Lemma.Int.Div.eq.AddDiv___Mod
import Lemma.Int.GeDivS.of.Gt_0
import Lemma.Int.Div.lt.One.of.Gt_0
import Lemma.Int.Lt_Add.of.Eq_Add.Lt
import Lemma.Int.EqFloor.is.Le.Lt
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
    apply Lt_Add.of.Eq_Add.Lt
    .
      apply Div.eq.AddDiv___Mod n d
    .
      apply Div.lt.One.of.Gt_0 (n := n) h


-- created on 2025-10-08
