import Lemma.Int.FDiv.eq.FloorDiv
import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Rat.Le_Div.of.LeMul.Gt_0
import Lemma.Int.DivInt.eq.Div
import Lemma.Int.LtCoeS.is.Lt
import Lemma.Rat.Div.lt.Zero.of.Lt_0.Gt_0
open Int Rat


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d > 0) :
-- imply
  -1 // d = -1 := by
-- proof
  have := GtCoeS.of.Gt (R := ℚ) h
  rw [FDiv.eq.FloorDiv (α := ℚ)]
  apply EqFloor.of.Le.Lt
  ·
    norm_cast
    simp
    rw [DivInt.eq.Div]
    apply Le_Div.of.LeMul.Gt_0
    ·
      simp
      norm_cast
    ·
      assumption
  ·
    norm_cast
    simp
    rw [DivInt.eq.Div]
    apply Div.lt.Zero.of.Lt_0.Gt_0
    norm_num
    assumption


-- created on 2025-03-30
-- updated on 2025-04-26
