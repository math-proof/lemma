import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.EqMulDiv
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqRepeatS.of.Eq
import Lemma.Tensor.EqSumS.of.Eq
import Lemma.Tensor.EqUnsqueezeS.of.Eq
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDot.eq.DotGet.of.Gt
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0
import Lemma.Tensor.GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.Get_0.eq.TensorCast_Data
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.Matmul.eq.Cast_BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.eq.SelectBatchDot.of.Eq_Get_SubLength.GeLength_2
import Lemma.Tensor.Select_0.eq.Cast_Get.of.GtLength_0
import Lemma.Vector.Cast_Cast.eq.Cast.of.Eq.Eq
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.Repeat.eq.Cast.of.Eq_1
open List Tensor Nat Vector


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : k ≥ n')
  (X : Tensor α [n, k])
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) = X[i] @ Y := by
-- proof
  if h_n : k = n' then
    subst h_n
    simp [GetElem.getElem]
    simp [MatMul.dot]
    rw [Matmul.eq.Cast_BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2]
    ·
      simp
      rw [Matmul.eq.SelectBatchDot.of.Eq_Get_SubLength.GeLength_2 (by simp) (by simp)]
      simp
      let XiBroadcast : Tensor α ([] ++ [1, k]) := (X.get i).broadcast [1, k] (by simp)
      have := Select_0.eq.Cast_Get.of.GtLength_0 (by grind) ⟨0, by simp⟩ (XiBroadcast.batch_dot Y)
      simp [XiBroadcast] at this
      rw [this]
      unfold broadcast_matmul
      simp [broadcast_matmul_rec]
      unfold Tensor.broadcast
      unfold batch_dot
      simp [broadcast_shape]
      simp [GetSum_2.eq.SumGet__1.fin]
      simp [@Tensor.GetMul.eq.MulGetS.fin]
      apply EqSumS.of.Eq
      have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
        (by simp)
        (show [n * 1, k', k] = [n, k', k] by simp)
        ((Yᵀ.unsqueeze 0).repeat n (0 : Fin 3))
        ⟨i, by simp⟩
      simp at this
      rw [this]
      have := GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0.fin (by grind) (by grind) (Yᵀ.unsqueeze 0) (i := 0) (n := 1)
      simp at this
      rw [this]
      have := GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0.fin (by grind) (by grind) (Yᵀ.unsqueeze 0) (i := i) (n := n)
      simp at this
      rw [this]
      simp [EqMod_1'0]
      apply EqMulS.of.Eq
      have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
        (by simp)
        (show [n, k' * 1, k] = [n, k', k] by simp)
        ((X.unsqueeze 1).repeat k' (1 : Fin 3))
        ⟨i, by simp⟩
      simp at this
      rw [this]
      have := GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0.fin (by grind) (by grind) (X.unsqueeze 1) k' (i := i) (d := ⟨1, by grind⟩)
      simp at this
      rw [this]
      have := GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind) X (i := i) (d := 1)
      simp at this
      rw [this]
      have h_s_prod : 1 * (k * 1) / (k * 1) * [n, k].tail.prod = [1, k].prod := by simp [EqMulDiv]
      have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
        (by simp)
        (show [1, k' * 1, k] = [1, k', k] by simp)
        (((⟨cast (congrArg (List.Vector α) h_s_prod) ((X.get i).data.repeat (1 * (k * 1) / (k * 1)))⟩ : Tensor α [1, k]).unsqueeze 1).repeat k' (1 : Fin 3))
        ⟨0, by simp⟩
      simp at this
      rw [this]
      have := GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0.fin
        (by grind)
        (by simp)
        ((⟨cast (congrArg (List.Vector α) h_s_prod) ((X.get i).data.repeat (1 * (k * 1) / (k * 1)))⟩ : Tensor α [1, k]).unsqueeze 1)
        k'
        (i := 0)
        (d := ⟨1, by simp⟩)
      simp at this
      rw [this]
      have := GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin (by simp) (by grind) (by grind) ((⟨cast (congrArg (List.Vector α) h_s_prod) ((X.get i).data.repeat (1 * (k * 1) / (k * 1)))⟩ : Tensor α [1, k])) (i := 0) (d := 1)
      simp at this
      simp [this]
      apply EqRepeatS.of.Eq
      apply EqUnsqueezeS.of.Eq
      if h_k : k = 0 then
        subst h_k
        simp
        apply Eq.of.EqDataS
        repeat rw [DataGet.eq.GetUnflattenData.fin]
        apply @Vector.Eq.of.All_EqGetS.fin
        intro t
        have h_t := t.isLt
        simp at h_t
      else
        rw [Repeat.eq.Cast.of.Eq_1]
        ·
          rw [Cast_Cast.eq.Cast.of.Eq.Eq]
          ·
            rw [Get_0.eq.TensorCast_Data]
            simp
            rfl
          ·
            rw [EqDivMul.of.Ne_0 (by omega)]
            simp
          ·
            rw [EqDivMul.of.Ne_0 (by omega)]
        ·
          rw [EqDivMul.of.Ne_0 (by omega)]
    ·
      simp
    ·
      simp
    ·
      simp
  else
    apply GetDot.eq.DotGet.of.Gt (by omega)


-- created on 2026-01-13
