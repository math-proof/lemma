import Lemma.Int.Div.eq.AddDiv___Mod
import Lemma.Algebra.EqCeil.is.Lt.Le
import Lemma.Algebra.Div.gt.Neg1.of.Lt_0
import Lemma.Algebra.Gt_Add.of.Eq_Add.Gt
import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Int.LeDivS.of.Lt_0
open Algebra Int


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d < 0) :
-- imply
  n / d = ⌈n / (d : ℚ)⌉ := by
-- proof
  apply Eq.symm
  rw [EqCeil.is.Lt.Le]
  constructor
  have h_Eq := Div.eq.AddDiv___Mod (n := n) (d := d)
  have := Div.gt.Neg1.of.Lt_0 (n := n) h
  have := Gt_Add.of.Eq_Add.Gt h_Eq this
  rwa [Add_Neg.eq.Sub] at this
  exact LeDivS.of.Lt_0 h


-- created on 2025-03-20
