import Lemma.Tensor.GetIte.eq.IteGetS
import Lemma.Tensor.GetDot.eq.DotGet.of.Lt
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.EqMulDiv
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.EqRepeatS.of.Eq
import Lemma.Tensor.EqSumS.of.Eq
import Lemma.Tensor.EqUnsqueezeS.of.Eq
import Lemma.Tensor.GetAppend.eq.Cast_AppendCastS_Get.of.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0
import Lemma.Tensor.GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.Get_0.eq.TensorCast_Data
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.Matmul.eq.Cast_BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.eq.SelectBatchDot.of.Lt_Get_SubLength.GeLength_2
import Lemma.Tensor.SEqDataS.of.SEq
import Lemma.Tensor.Select_0.eq.Cast_Get.of.GtLength_0
import Lemma.Vector.Cast_Cast.eq.Cast.of.Eq.Eq
import Lemma.Vector.Repeat.eq.Cast.of.Eq_1
open Bool List Nat Tensor Vector
set_option maxHeartbeats 1000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : k < n')
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) ≃ X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  match s with
  | [] =>
    rw [Tensor.GetDot.eq.DotGet.of.Lt.fin h]
  | s₀ :: s =>
    simp [MatMul.dot]
    have := Matmul.eq.Cast_BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa) X Y
    have := Tensor.EqGetS.of.Eq.GtLength_0 (by simp [matmul_shape]) this ⟨i, by simp [matmul_shape, broadcast_shape]⟩
    simp [this]
    rw [Matmul.eq.Cast_BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa)]
    simp
    apply SEq_Cast.of.SEq.Eq (by simp [matmul_shape, broadcast_shape])
    unfold broadcast_matmul
    simp
    -- simp [broadcast_matmul_rec]
    unfold broadcast
    simp [broadcast_shape]
    split_ifs with h
    .
      have h' : ((n :: s₀ :: (s ++ [k])).take ((s ++ [k]).length + 1 + 1 - 2)).length > 0 := by
        simp
      -- simp [Tensor.GetIte.eq.IteGetS.fin]
      -- simp [h']
      sorry
    .
      sorry


-- created on 2026-01-11
