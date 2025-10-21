import Lemma.Algebra.SquareSub.eq.SubAddSquareS_MulMul2
import Lemma.Algebra.GtSqrtS.of.Gt.Gt_0
import Lemma.Int.Sub.gt.Zero.is.Gt
import Lemma.Algebra.GtSquare_0.of.Gt_0
import Lemma.Algebra.EqSquareSqrt.of.Gt_0
import Lemma.Int.AddSub.eq.SubAdd
open Algebra Int


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 1) :
-- imply
  x - 2 * √x + 1 > 0 := by
-- proof
  have := SquareSub.eq.SubAddSquareS_MulMul2 (a := √x) (b := 1)
  norm_num at this
  have h_Sqrt := GtSqrtS.of.Gt.Gt_0 h (by linarith [h])
  norm_num at h_Sqrt
  have h_Sqrt := Sub.gt.Zero.of.Gt h_Sqrt
  have h_Gt_0 := GtSquare_0.of.Gt_0 (a := √x - 1) h_Sqrt
  rw [this] at h_Gt_0
  have := EqSquareSqrt.of.Gt_0 (by linarith [h] : x > 0)
  rw [this] at h_Gt_0
  rwa [SubAdd.eq.AddSub] at h_Gt_0


-- created on 2025-04-06
