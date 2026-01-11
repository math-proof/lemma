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
  (X : Tensor α [n, k])
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) = X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  simp [MatMul.dot]
  rw [Matmul.eq.Cast_BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2]
  ·
    simp
    rw [Matmul.eq.SelectBatchDot.of.Lt_Get_SubLength.GeLength_2]
    ·
      simp
      let Xi : Tensor α ([n' / k * k]) := (X.get i).repeat (n' / k) (0 : Fin 1)
      let XiAppend : Tensor α [n' / k * k + n' % k] := Xi ++ (0 : Tensor α [n' % k])
      have h_s : [n' / k * k + n' % k] = [n'] := by simp [EqAddMulDiv]
      let XiAppendBroadcast : Tensor α ([] ++ [1, n']) := (cast (congrArg (Tensor α) h_s) XiAppend).broadcast [1, n'] (by simp)
      have := Select_0.eq.Cast_Get.of.GtLength_0 (by grind) ⟨0, by simp⟩ (XiAppendBroadcast.batch_dot Y)
      simp [XiAppendBroadcast] at this
      rw [this]
      unfold broadcast_matmul
      simp [broadcast_matmul_rec]
      unfold Tensor.broadcast
      unfold batch_dot
      simp [broadcast_shape]
      simp [GetSum_2.eq.SumGet__1.fin]
      simp [@Tensor.GetMul.eq.MulGetS.fin]
      apply EqSumS.of.Eq
      have := GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0.fin (by grind) (by grind) (Yᵀ.unsqueeze 0) (i := 0) (n := 1)
      simp at this
      rw [this]
      have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
        (by simp)
        (show [n * 1, k', n'] = [n, k', n'] by simp)
        ((Yᵀ.unsqueeze 0).repeat n (0 : Fin 3))
        ⟨i, by simp⟩
      simp at this
      rw [this]
      have := GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0.fin (by grind) (by grind) (Yᵀ.unsqueeze 0) (i := i) (n := n)
      simp at this
      rw [this]
      simp [EqMod_1'0]
      apply EqMulS.of.Eq
      let X' : Tensor α ([] ++ [n] ++ [n' / k * k]) := X.repeat (n' / k) (1 : Fin 2)
      let X'Append : Tensor α [n, n' / k * k + n' % k] := X' ++ (0 : Tensor α ([] ++ [n] ++ [n' % k]))
      have h_s_list : [n, n' / k * k + n' % k] = [n, n'] := by simp [EqAddMulDiv]
      have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
        (by simp)
        (show [n, k' * 1, n'] = [n, k', n'] by simp)
        (((cast (congrArg (Tensor α) h_s_list) X'Append).unsqueeze 1).repeat k' (1 : Fin 3))
        ⟨i, by simp⟩
      simp at this
      rw [this]
      have := GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0.fin (by grind) (by grind) ((cast (congrArg (Tensor α) h_s_list) X'Append).unsqueeze 1) k' (i := i) (d := ⟨1, by grind⟩)
      simp at this
      rw [this]
      have := GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin (by grind) (by grind) (by grind) (cast (congrArg (Tensor α) h_s_list) X'Append) (i := i) (d := 1)
      simp at this
      rw [this]
      have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by simp) h_s_list X'Append ⟨i, by simp⟩
      simp at this
      rw [this]
      simp [X'Append]
      have := GetAppend.eq.Cast_AppendCastS_Get.of.GtLength_0.fin (by grind) X' (0 : Tensor α ([] ++ [n] ++ [n' % k])) ⟨i, by simp⟩
      simp at this
      rw [this]
      rw [@Tensor.EqGet0_0.fin]
      have h_s_prod : ([1, n'].prod / [n'].prod * [n'].prod) = [1, n'].prod := by simp [EqMulDiv]
      have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
        (by simp)
        (show [1, k' * 1, n'] = [1, k', n'] by simp)
        (((⟨cast (congrArg (List.Vector α) h_s_prod) ((cast (congrArg (Tensor α) h_s) XiAppend).data.repeat (1 * (n' * 1) / (n' * 1)))⟩ : Tensor α [1, n']).unsqueeze 1).repeat k' (1 : Fin 3))
        ⟨0, by simp⟩
      simp at this
      rw [this]
      have := GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0.fin (by grind) (by simp) ((⟨cast (congrArg (List.Vector α) h_s_prod) ((cast (congrArg (Tensor α) h_s) XiAppend).data.repeat (1 * (n' * 1) / (n' * 1)))⟩ : Tensor α [1, n']).unsqueeze 1) k' (i := 0) (d := ⟨1, by simp⟩)
      simp at this
      rw [this]
      have := GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin (by simp) (by grind) (by grind) ((⟨cast (congrArg (List.Vector α) h_s_prod) ((cast (congrArg (Tensor α) h_s) XiAppend).data.repeat (1 * (n' * 1) / (n' * 1)))⟩ : Tensor α [1, n'])) (i := 0) (d := 1)
      simp at this
      simp [this]
      rw [DataCast.eq.Cast_Data.of.Eq]
      ·
        simp [XiAppend, Xi, X']
        rw [Repeat.eq.Cast.of.Eq_1]
        ·
          repeat rw [Cast_Cast.eq.Cast.of.Eq.Eq]
          ·
            rw [Get_0.eq.TensorCast_Data]
            simp
            have := GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0.fin (by grind) (by simp) X (n' / k) (i := i) (d := ⟨1, by simp⟩)
            simp at this
            rw [this]
            apply EqRepeatS.of.Eq
            apply EqUnsqueezeS.of.Eq
            apply Eq.of.EqDataS
            simp
            apply Eq_Cast.of.SEq.Eq
            ·
              simp [EqAddMulDiv]
            ·
              apply SEqDataS.of.SEq
              apply SEqCast.of.SEq.Eq
              ·
                simp [EqAddMulDiv]
              ·
                rfl
          ·
            simp [EqAddMulDiv]
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
        simp [EqAddMulDiv]
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
