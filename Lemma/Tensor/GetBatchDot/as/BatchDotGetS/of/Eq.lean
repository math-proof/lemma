import Lemma.Tensor.GetBatchDot.eq.BatchDotGetS
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthBatchDot.eq.Length
import Lemma.Tensor.SEqBatchDotS.of.SEq.SEq
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
open Tensor


@[main, fin, cast, cast.fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : bz = b₀ :: b)
  (X : Tensor α (bz ++ [m, k]))
  (Y : Tensor α (bz ++ [k, n]))
  (i : Fin b₀) :
-- imply
  have h_X : bz ++ [m, k] = (b₀ :: b) ++ [m, k] := by
    rw [h]
  have h_Y : bz ++ [k, n] = (b₀ :: b) ++ [k, n] := by
    rw [h]
  let X' := cast (congrArg (Tensor α) h_X) X
  let Y' := cast (congrArg (Tensor α) h_Y) Y
  have h_i : i < (X.bmm Y).length := by
    rw [LengthBatchDot.eq.Length]
    rw [Length.eq.Get_0.of.GtLength_0 (by simp)]
    grind
  (X.bmm Y)[i] ≃ X'[i].bmm Y'[i] := by
-- proof
  intros h_X h_Y X' Y' h_i
  rw [← GetBatchDot.eq.BatchDotGetS]
  simp [X', Y']
  simp [GetElem.getElem]
  apply SEqGetS.of.SEq.GtLength
  apply SEqBatchDotS.of.SEq.SEq
  repeat aesop


-- created on 2026-07-03
-- updated on 2026-07-04
