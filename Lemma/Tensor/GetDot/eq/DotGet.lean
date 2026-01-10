import Lemma.Nat.EqMulDiv
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.GetAppend.eq.Cast_AppendCastS_Get.of.GtLength_0
import Lemma.Tensor.GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Nat.EqMod_1'0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Lt_Get_0.Eq.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.EqGetUnsqueeze
import Lemma.Tensor.GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Nat.EqAddMulDiv
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.Matmul.eq.Cast_BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.eq.Cast_BroadcastMatmul.of.GtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.eq.Cast_BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.eq.SelectBatchDot.of.Eq_Get_SubLength.GeLength_2
import Lemma.Tensor.Matmul.eq.SelectBatchDot.of.Gt_Get_SubLength.GeLength_2
import Lemma.Tensor.Matmul.eq.SelectBatchDot.of.Lt_Get_SubLength.GeLength_2
import Lemma.Tensor.Select_0.eq.Cast_Get.of.GtLength_0
open List Tensor Nat
set_option maxHeartbeats 1000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n, k])
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil h_s (by apply GeLength_1.of.Ne_Nil h_s) X Y i) = X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  simp [MatMul.dot]
  if h_n : k < n' then
    rw [Matmul.eq.Cast_BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2]
    ·
      simp
      rw [Matmul.eq.SelectBatchDot.of.Lt_Get_SubLength.GeLength_2]
      ·
        simp
        let Xi : Tensor α ([n' / k * [k][0]]) := (X.get i).repeat (n' / k) (0 : Fin (0 + 1))
        have h_Xi : Xi = (X.get i).repeat (n' / k) (0 : Fin (0 + 1)) := rfl
        simp [← h_Xi]
        let XiAppend : Tensor α [n' / k * k + n' % k] := Xi ++ (0 : Tensor α [[n', k'][[n', k'].length - 2] % k])
        have h_XiAppend : XiAppend = Xi ++ (0 : Tensor α [[n', k'][[n', k'].length - 2] % k]) := rfl
        simp [← h_XiAppend]
        have h_s : [[n', k'][[n', k'].length - 2] / k * k + [n', k'][[n', k'].length - 2] % k] = [[n', k'][[n', k'].length - 2]] := by simp [EqAddMulDiv]
        let XiAppendBroadcast : Tensor α ([] ++ [1, n']) := (cast (congrArg (Tensor α) h_s) XiAppend).broadcast [1, n'] (by simp)
        have := Select_0.eq.Cast_Get.of.GtLength_0 (by grind) ⟨0, by simp⟩ (XiAppendBroadcast.batch_dot Y)
        simp [XiAppendBroadcast] at this
        rw [this]
        unfold Tensor.broadcast_matmul
        simp
        simp [Tensor.broadcast_matmul_rec]
        unfold Tensor.broadcast
        simp
        unfold Tensor.batch_dot
        simp [broadcast_shape]
        simp [GetSum_2.eq.SumGet__1.fin]
        simp [GetMul.eq.MulGetS.fin]
        have := GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0.fin (by grind) (by grind) (Yᵀ.unsqueeze 0) (i := 0) (n := 1)
        simp at this
        rw [this]
        have h_s_broadcast_shape : ((broadcast_shape [] [] ++ [1, k', n']).set (broadcast_shape [] []).length (n * (broadcast_shape [] [] ++ [1, k', n'])[(broadcast_shape [] []).length])) = (broadcast_shape [] [] ++ [n, k', n']) := by
          simp [broadcast_shape]
        have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by simp [broadcast_shape]) h_s_broadcast_shape ((Yᵀ.unsqueeze 0).repeat n (0 : Fin (2 + 1))) ⟨i, by simp [broadcast_shape]⟩
        simp at this
        rw [this]
        have := GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0.fin (by grind) (by grind) (Yᵀ.unsqueeze 0) (i := i) (n := n)
        simp at this
        rw [this]
        simp [EqMod_1'0]
        have := EqGetUnsqueeze.fin Yᵀ
        simp at this
        rw [this]
        let X' : Tensor α ([] ++ [n] ++ [n' / k * [n, k][1]]) := X.repeat (n' / k) (1 : Fin (([] : List ℕ).length + 2))
        have h_X' : X' = X.repeat (n' / k) (1 : Fin (([] : List ℕ).length + 2)) := rfl
        rw [← h_X']
        let X'Append : Tensor α [n, n' / k * k + n' % k] := X' ++ (0 : Tensor α ([] ++ [n] ++ [n' % k]))
        have h_X'Append : X'Append = X' ++ (0 : Tensor α ([] ++ [n] ++ [n' % k])) := rfl
        rw [← h_X'Append]
        have h_s_list : [n, n' / k * k + n' % k] = [n, n'] := by simp [EqAddMulDiv]
        have h_s' : ((broadcast_shape [] [] ++ [n, 1, n']).set ((broadcast_shape [] []).length + 1) (k' * (broadcast_shape [] [] ++ [n, 1, n'])[(broadcast_shape [] []).length + 1])) = (broadcast_shape [] [] ++ [n, k', n']) := by simp [broadcast_shape]
        have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by simp) h_s' (((cast (congrArg (Tensor α) h_s_list) X'Append).unsqueeze 1).repeat k' (1 : Fin (1 + 2))) ⟨i, by simp [broadcast_shape]⟩
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
        rw [EqGet0_0.fin]
        have h_s_prod : ([1, n'].prod / [n'].prod * [n'].prod) = [1, n'].prod := by simp [Nat.EqMulDiv]
        have h_s' : ([] ++ [1, 1, n']).set (([] : List ℕ).length + 1) (k' * ([] ++ [1, 1, n'])[([] : List ℕ).length + 1]) = [] ++ [1, k', n'] := by
          simp
        have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
          (by simp)
          h_s'
          (((⟨cast (congrArg (List.Vector α) h_s_prod) ((cast (congrArg (Tensor α) h_s) XiAppend).data.repeat (1 * (n' * 1) / (n' * 1)))⟩ : Tensor α [1, n']).unsqueeze 1).repeat k' (1 : Fin (1 + 2)))
          ⟨0, by simp⟩
        simp at this
        rw [this]
        have := GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0.fin (by grind) (by simp) ((⟨cast (congrArg (List.Vector α) h_s_prod) ((cast (congrArg (Tensor α) h_s) XiAppend).data.repeat (1 * (n' * 1) / (n' * 1)))⟩ : Tensor α [1, n']).unsqueeze 1) k' (i := 0) (d := ⟨1, by simp⟩)
        simp at this
        rw [this]
        have := GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin (by simp) (by grind) (by grind) ((⟨cast (congrArg (List.Vector α) h_s_prod) ((cast (congrArg (Tensor α) h_s) XiAppend).data.repeat (1 * (n' * 1) / (n' * 1)))⟩ : Tensor α [1, n'])) (i := 0) (d := 1)
        simp at this
        simp [this]
        rw [Tensor.DataCast.eq.Cast_Data.of.Eq]
        .
          simp [XiAppend, Xi, X']
          sorry
        .
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
  else if h_n : k > n' then
    rw [Matmul.eq.Cast_BroadcastMatmul.of.GtGetS_SubLength.GeLength_2.GeLength_2]
    ·
      simp
      rw [Matmul.eq.SelectBatchDot.of.Gt_Get_SubLength.GeLength_2]
      ·
        simp
        sorry
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
  else
    have h_n : k = n' := by omega
    rw [Matmul.eq.Cast_BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2]
    ·
      simp
      rw [Matmul.eq.SelectBatchDot.of.Eq_Get_SubLength.GeLength_2]
      ·
        simp
        sorry
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


-- created on 2026-01-05
-- updated on 2026-01-10
