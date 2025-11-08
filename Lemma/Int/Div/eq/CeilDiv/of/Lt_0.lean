import Lemma.Int.Div.eq.AddDiv___Mod
import Lemma.Rat.EqCeil.is.Lt.Le
import Lemma.Int.Div.gt.Neg1.of.Lt_0
import Lemma.Nat.Gt_Add.of.Eq_Add.Gt
import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Int.LeDivS.of.Lt_0
open Int Rat Nat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℤ}
-- given
  (h : d < 0) :
-- imply
  n / d = ⌈n / (d : α)⌉ := by
-- proof
  apply Eq.symm
  rw [EqCeil.is.Lt.Le]
  constructor
  have h_Eq := Div.eq.AddDiv___Mod n d (α := α)
  have := Div.gt.Neg1.of.Lt_0 (n := n) h (α := α)
  have := Gt_Add.of.Eq_Add.Gt h_Eq this
  rwa [Add_Neg.eq.Sub] at this
  exact LeDivS.of.Lt_0 h


-- created on 2025-03-20
