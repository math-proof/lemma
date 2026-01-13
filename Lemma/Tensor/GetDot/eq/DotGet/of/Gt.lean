import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqSumS.of.Eq
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0
import Lemma.Tensor.GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.Get_0.eq.TensorCast_Data
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.Matmul.eq.Cast_BroadcastMatmul.of.GtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.eq.SelectBatchDot.of.Gt_Get_SubLength.GeLength_2
import Lemma.Tensor.Select_0.eq.Cast_Get.of.GtLength_0
import Lemma.Vector.Cast_Cast.eq.Cast.of.Eq.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.Repeat.eq.Cast.of.Eq_1
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Fin Bool List Nat Tensor Vector
set_option maxHeartbeats 1000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : k > n')
  (X : Tensor α [n, k])
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) = X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  simp [MatMul.dot]
  rw [Matmul.eq.Cast_BroadcastMatmul.of.GtGetS_SubLength.GeLength_2.GeLength_2]
  ·
    simp
    rw [Matmul.eq.SelectBatchDot.of.Gt_Get_SubLength.GeLength_2]
    ·
      simp
      let Y' : Tensor α [k / n' * n', k'] := Y.repeat (k / n') (0 : Fin 2)
      let Y'Append : Tensor α [k / n' * n' + k % n', k'] := Y' ++ (0 : Tensor α [k % n', k'])
      have h_s : [k / n' * n' + k % n', k'] = [k, k'] := by simp [EqAddMulDiv]
      let XiBroadcast : Tensor α ([] ++ [1, k]) := (X.get i).broadcast [1, k] (by simp)
      have := Select_0.eq.Cast_Get.of.GtLength_0 (by grind) ⟨0, by simp⟩ (XiBroadcast.batch_dot (cast (congrArg (Tensor α) h_s) Y'Append))
      simp [XiBroadcast] at this
      rw [this]
      unfold Tensor.broadcast_matmul
      simp [broadcast_matmul_rec]
      unfold Tensor.broadcast
      unfold Tensor.batch_dot
      simp [broadcast_shape]
      simp [GetSum_2.eq.SumGet__1.fin]
      simp [@Tensor.GetMul.eq.MulGetS.fin]
      apply EqSumS.of.Eq
      have := GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0.fin (by grind) (by grind) ((cast (congrArg (Tensor α) h_s) Y'Append)ᵀ.unsqueeze 0) (i := 0) (n := 1)
      simp at this
      rw [this]
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
      have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
        (by simp)
        (show [n * 1, k', k] = [n, k', k] by simp)
        (((cast (congrArg (Tensor α) h_s) Y'Append)ᵀ.unsqueeze 0).repeat n (0 : Fin 3))
        ⟨i, by simp⟩
      simp at this
      rw [this]
      have := GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0.fin (by grind) (by grind) ((cast (congrArg (Tensor α) h_s) Y'Append)ᵀ.unsqueeze 0) (i := i) (n := n)
      simp at this
      rw [this]
      simp [EqMod_1'0]
      apply EqMulS.of.Eq
      rw [Get_0.eq.TensorCast_Data]
      apply Eq.of.EqDataS
      simp
      apply Eq_Cast.of.SEq.Eq (by simp)
      repeat rw [DataCast.eq.Cast_Data.of.Eq (by simp)]
      apply SEqCastS.of.SEq.Eq.Eq (by simp) (by simp)
      have := GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind) X (i := i) (d := 1)
      simp at this
      rw [this]
      rw [Repeat.eq.Cast.of.Eq_1]
      ·
        rw [Cast_Cast.eq.Cast.of.Eq.Eq]
        ·
          unfold Tensor.unsqueeze
          simp
          unfold Tensor.repeat
          simp
          apply SEq.of.All_EqGetS.Eq.fin
          ·
            intro t
            have h_t := t.isLt
            repeat rw [GetCast.eq.Get.of.Eq.fin]
            ·
              simp
              have h_t : t < 1 * (k' * (1 * (k * 1))) := by
                simp_all
              let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
              repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
              simp
              repeat rw [GetRepeat.eq.Get_Mod.fin]
              simp
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              simp
              repeat rw [GetCast.eq.Get.of.Eq.fin]
              ·
                simp
              ·
                simp
            ·
              simp
            ·
              simp
          ·
            simp
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
      simpa
  ·
    simp
  ·
    simp
  ·
    simpa


-- created on 2026-01-10
-- updated on 2026-01-11
