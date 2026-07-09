import Lemma.Fin.Eq_0
import Lemma.List.EqSwap_0'1
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Div.eq.One.of.Ne_0
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.EqMulDiv
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Tensor.DataAppend.as.AppendDataS
import Lemma.Tensor.DataCast.as.Data.of.Eq
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataRepeat.as.FlattenMapSplitAtData
import Lemma.Tensor.DataTransposeTensor.eq.Cast
import Lemma.Tensor.DataUnsqueeze.as.Data
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqRepeatS.of.Eq
import Lemma.Tensor.EqSumS.of.Eq
import Lemma.Tensor.EqUnsqueezeS.of.Eq
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDot.eq.DotGet.of.Gt
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.GetSelect_1.as.Get.of.Lt_Get_0.Lt_Get_1.GtLength_1
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.Get_0.eq.TensorCast_Data
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.HeadDataSum.eq.SumData
import Lemma.Tensor.Matmul.as.BroadcastMatmul.of.EqGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.as.SelectBatchDot.of.EqGet_SubLength_1.GeLength_2
import Lemma.Tensor.Matmul.as.SelectBatchDot.of.Eq_Get_SubLength.GeLength_2
import Lemma.Tensor.Matmul.eq.Zero
import Lemma.Tensor.Select_0.as.Get.of.GtLength_0
import Lemma.Tensor.Sum.eq.Zero
import Lemma.Vector.Cast_Cast.eq.Cast.of.Eq.Eq
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.EqSumS.of.SEq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.Repeat.eq.Cast.of.Eq_1
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Fin List Nat Tensor Vector
set_option maxHeartbeats 1000000


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
      rw [Matmul.eq.Cast_SelectBatchDot.of.Eq_Get_SubLength.GeLength_2 (by simp) (by simp)]
      simp
      let XiBroadcast : Tensor α ([] ++ [1, k]) := (X.get i).broadcast [1, k] (by simp)
      have := Select_0.eq.Cast_Get.of.GtLength_0 (by grind) (XiBroadcast.batch_dot Y) ⟨0, by simp⟩
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
      have := GetRepeat.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind) (Yᵀ.unsqueeze 0) (i := 0) (n := 1)
      simp at this
      rw [this]
      have := GetRepeat.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind) (Yᵀ.unsqueeze 0) (i := i) (n := n)
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


@[main, fin]
private lemma une
  [Mul α] [AddCommMonoid α]
-- given
  (h : k ≥ n')
  (X : Tensor α [n, k])
  (Y : Tensor α [n'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by simp) X Y i) = X[i] @ Y := by
-- proof
  if hk : k = n' then
    subst hk
    if hn0 : k = 0 then
      subst hn0
      simp [GetElem.getElem, MatMul.dot]
      rw [Matmul.eq.Cast_SelectBatchDot.of.EqGet_SubLength_1.GeLength_2 (by simp) (by rfl)]
      simp [Tensor.batch_dot, Tensor.broadcast, matmul_shape]
      apply Eq.of.EqDataS
      apply @Vector.Eq.of.All_EqGetS.fin
      intro t
      have h_t := Eq_0 t
      subst h_t
      simp
      repeat apply congrArg
      rw [Matmul.eq.Zero]
      let Xl : Tensor α [n, 1, 0] := (X.unsqueeze 1).repeat 1 ⟨1, by grind⟩
      let Xr : Tensor α [n, 1, 0] := cast (congrArg (Tensor α) (by simp [EqSwap_0'1])) (((⟨Y.data.repeat 0⟩ : Tensor α [0, 1])ᵀ.unsqueeze 0).repeat n ⟨0, by grind⟩)
      have := GetSelect_1.eq.Cast_Get.of.Lt_Get_0.Lt_Get_1.GtLength_1 (by simp) (by simp) (by grind) ((Xl * Xr).sum 2) (i := 0) (j := i)
      simp [Xl, Xr] at this
      rw [this]
      rw [GetSum_2.eq.SumGet__0.fin]
      rw [@Tensor.Sum.eq.Zero]
    else
      have h_k : k ≠ 0 := hn0
      simp [GetElem.getElem]
      simp [MatMul.dot]
      rw [Matmul.eq.Cast_SelectBatchDot.of.EqGet_SubLength_1.GeLength_2 (by simp) (by rfl)]
      ·
        simp
        unfold Tensor.broadcast Tensor.batch_dot
        simp
        have h_s0 : ([] ++ [1, 1, k]).set ([] : List ℕ).length (n * ([] ++ [1, 1, k])[([] : List ℕ).length]) = [n, 1, k] := by
          simp
        have h_s1 : [k, 1].prod / [k].prod * [k].prod = [k, 1].prod := by
          simp [EqMulDiv]
        have h_q : k / k = 1 := Nat.div_self (Nat.pos_of_ne_zero h_k)
        have h_r : k % k = 0 := Nat.mod_self k
        let Y' : Tensor α [k / k * k] := Y.repeat (k / k) (0 : Fin 1)
        let Y'Append : Tensor α [k / k * k + k % k] := Y' ++ (0 : Tensor α [k % k])
        let X' : Tensor α [n, 1, k] := (X.unsqueeze 1).repeat 1 (1 : Fin 3)
        have := GetSelect_1.eq.Cast_Get.of.Lt_Get_0.Lt_Get_1.GtLength_1
          (by grind)
          (by grind)
          (by grind)
          ((X' * cast (congrArg (Tensor α) h_s0)
            (((⟨cast (congrArg (List.Vector α) h_s1) (Y.data.repeat (k * 1 / (k * 1)))⟩ : Tensor α _)ᵀ.unsqueeze 0).repeat n (0 : Fin 3)
            )).sum 2
          )
          (i := 0) (j := i)
        simp at this
        rw [this]
        rw [GetSum_2.eq.SumGet__0.fin, @Tensor.GetMul.eq.MulGetS.fin]
        have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
          (by grind)
          (by simp [EqSwap_0'1]; grind)
          (((⟨cast (congrArg (List.Vector α) h_s1) (Y.data.repeat (k * 1 / (k * 1)))⟩ : Tensor α _)ᵀ.unsqueeze 0).repeat n (0 : Fin 3))
          ⟨i, by grind⟩
          (s' := [n, 1, k])
        simp at this
        rw [this]
        apply Eq.of.EqDataS
        simp
        rw [Repeat.eq.Cast.of.Eq_1]
        ·
          rw [Cast_Cast.eq.Cast.of.Eq.Eq]
          ·
            unfold Tensor.unsqueeze Tensor.repeat
            simp
            apply @Vector.Eq.of.All_EqGetS.fin
            intro t
            have h_t := Eq_0 t
            subst h_t
            simp [@Tensor.GetMul.eq.MulGetS.fin]
            conv_rhs => simp [List.Vector.head, DataCast.eq.Cast_Data.of.Eq, DataAppend.eq.Cast_AppendDataS]
            simp [X']
            rw [HeadDataSum.eq.SumData]
            apply EqSumS.of.SEq
            apply SEq.of.All_EqGetS.Eq.fin
            ·
              intro j
              have h_j := j.isLt
              simp at h_j
              have hnlt : ¬k < k := by omega
              have hdec : ¬(k + 1) ≤ k := by omega
              simp [Nat.decLt, Nat.decLe, hdec]
              simp [@Vector.GetMul.eq.MulGetS.fin]
              rw [DataCast.eq.Cast_Data.of.Eq (by grind)]
              conv_rhs =>
                arg 2
                rw [DataCast.eq.Cast_Data.of.Eq (by grind)]
              repeat rw [GetCast.eq.Get.of.Eq.fin (by grind)]
              rw [DataMul.eq.MulDataS]
              rw [@Vector.GetMul.eq.MulGetS.fin]
              repeat rw [DataGet.eq.GetUnflattenData.fin, GetUnflatten.eq.Get_AddMul.fin]
              simp
              rw [DataRepeat.eq.Cast_FlattenMapSplitAtData]
              rw [GetCast.eq.Get.of.Eq.fin (by simp)]
              simp
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨i, by grind⟩) (j := ⟨j, by grind⟩) (by simp)]
              simp [GetRepeat.eq.Get_Mod.fin]
              rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              simp [EqMod.of.Lt h_j]
              rw [DataUnsqueeze.eq.Cast_Data]
              rw [GetCast.eq.Get.of.Eq.fin (by simp)]
              apply EqMulS.of.Eq.left
              rw [GetCast.eq.Get.of.Eq.fin (by simp [EqSwap_0'1]; grind)]
              simp
              have h_ij := AddMul.lt.Mul.of.Lt.Lt i.isLt (show j < k by grind)
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨0, by grind⟩) (j := ⟨i * k + j, by simpa [EqSwap_0'1]⟩) (by simp)]
              simp [GetRepeat.eq.Get_Mod.fin, EqSwap_0'1, EqMod.of.Lt h_j]
              rw [Head.eq.Get_0.fin]
              rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              simp [DataTransposeTensor.eq.Cast]
              repeat rw [GetCast.eq.Get.of.Eq.fin (by simp [EqSwap_0'1])]
            ·
              simp
          ·
            grind
          ·
            grind
        ·
          simp [Div.eq.One.of.Ne_0 h_k]
  else
    apply GetDot.eq.DotGet.of.Gt.une
    omega


-- created on 2026-01-13
-- updated on 2026-07-06
