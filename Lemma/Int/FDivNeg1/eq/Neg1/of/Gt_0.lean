import Lemma.Int.FDiv.eq.FloorDiv
import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Rat.GeDiv.of.Ge_Mul.Gt_0
import Lemma.Algebra.DivInt.eq.Div
import Lemma.Int.GtCoeS.is.Gt
import Lemma.Algebra.Div.lt.Zero.of.Lt_0.Gt_0
open Algebra Int Rat


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d > 0) :
-- imply
  -1 // d = -1 := by
-- proof
  have := GtCoeS.of.Gt (R := ℚ) h
  rw [FDiv.eq.FloorDiv]
  apply EqFloor.of.Le.Lt
  ·
    norm_cast
    simp
    rw [DivInt.eq.Div]
    apply GeDiv.of.Ge_Mul.Gt_0
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
