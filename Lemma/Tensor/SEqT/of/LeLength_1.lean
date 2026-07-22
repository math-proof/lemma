import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.EqPermute
import Lemma.List.EqPermuteS__Neg.of.Le
import Lemma.List.EqSwap
import Lemma.Tensor.SEqPermute
import Lemma.Tensor.SEqPermuteS__Neg.of.Le
import Lemma.Tensor.T.as.Permute__Neg1.of.GtLength_0
open Bool List Tensor


@[main, cast]
private lemma main
-- given
  (h : s.length ≤ 1)
  (X : Tensor α s) :
-- imply
  Xᵀ ≃ X := by
-- proof
  if h : s.length = 1 then
    match s with
    | [n] =>
      rw [T.eq.Cast_Permute__Neg1.of.GtLength_0 (by grind)]
      apply SEqCast.of.SEq.Eq
      ·
        simp
        rw [EqSwap]
        erw [EqPermuteS__Neg.of.Le (by grind)]
        simp [EqPermute]
      ·
        simp
        erw [Permute__Neg.eq.Cast.of.Le (by grind)]
        simp
        apply SEqCast.of.SEq.Eq
        ·
          simp [EqPermute]
          erw [EqPermuteS__Neg.of.Le (by grind)]
          simp [EqPermute]
        ·
          apply SEqPermute
  else
    have h : s.length = 0 := by omega
    match s with
    | [] =>
      unfold Tensor.T
      simp
      unfold Tensor.transpose
      simp
      apply SEqCast.of.Eq
      rw [EqSwap]


-- created on 2026-07-22
