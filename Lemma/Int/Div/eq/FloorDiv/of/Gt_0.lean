import Lemma.Int.Div.eq.AddDiv___Mod
import Lemma.Int.GeDivS.of.Gt_0
import Lemma.Int.Div.lt.One.of.Gt_0
import Lemma.Int.Lt_Add.of.Eq_Add.Lt
import Lemma.Int.EqFloor.is.Le.Lt
open Int


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  n / d = ⌊n / (d : ℚ)⌋ := by
-- proof
  apply Eq.symm
  rw [EqFloor.is.Le.Lt]
  constructor
  · 
    exact GeDivS.of.Gt_0 h
  · 
    have h_Eq := Div.eq.AddDiv___Mod (n := n) (d := d)
    have := Div.lt.One.of.Gt_0 (n := n) h
    exact Lt_Add.of.Eq_Add.Lt h_Eq this


-- created on 2025-10-08
