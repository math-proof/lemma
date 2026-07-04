import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx
import Lemma.Tensor.LengthCast.eq.Length.of.Eq
import Lemma.Tensor.LengthMul.eq.Length.of.GtLength_0
import Lemma.Tensor.LengthRepeat.eq.Length.of.GtVal_0
import Lemma.Tensor.LengthSum.eq.Length.of.Gt_0
import Lemma.Tensor.LengthUnsqueeze.eq.Length.of.Gt_0
import sympy.tensor.tensor
open List Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α (bz ++ [m, k]))
  (Y : Tensor α (bz ++ [k, n])) :
-- imply
  (X.batch_dot Y).length = X.length := by
-- proof
  unfold Tensor.batch_dot
  rw [LengthCast.eq.Length.of.Eq (by grind)]
  rw [LengthSum.eq.Length.of.Gt_0 (by simp)]
  rw [LengthMul.eq.Length.of.GtLength_0 (by simp)]
  rw [LengthCast.eq.Length.of.Eq (by simp)]
  rw [LengthRepeat.eq.Length.of.GtVal_0 (by simp)]
  rw [LengthCast.eq.Length.of.Eq (by rw [InsertIdxAppend.eq.Append_InsertIdx]; grind)]
  simp [LengthUnsqueeze.eq.Length.of.Gt_0]


-- created on 2026-07-04
