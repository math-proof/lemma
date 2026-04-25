import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Fin.Eq_0
import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.List.ProdSwap.eq.Prod
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Div.eq.One.of.Ne_0
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.EqMulDiv
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Tensor.DataAppend.eq.Cast_AppendDataS
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataTransposeTensor.eq.Cast
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.EqRepeatS.of.Eq
import Lemma.Tensor.EqSumS.of.Eq
import Lemma.Tensor.EqUnsqueezeS.of.Eq
import Lemma.Tensor.GetAppend.eq.Cast_AppendCastS_Get.of.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0
import Lemma.Tensor.GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.Tensor.GetSelect_1.eq.Cast_Get.of.Lt_Get_0.Lt_Get_1.GtLength_1
import Lemma.Tensor.GetSum_2.eq.SumGet__0
import Lemma.Tensor.GetSum_2.eq.SumGet__1
import Lemma.Tensor.GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.Get_0.eq.TensorCast_Data
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import Lemma.Tensor.HeadDataSum.eq.SumData
import Lemma.Tensor.Matmul.eq.Cast_BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.eq.Cast_SelectBatchDot.of.LtGet_SubLength_1.GeLength_2
import Lemma.Tensor.Matmul.eq.SelectBatchDot.of.Lt_Get_SubLength.GeLength_2
import Lemma.Tensor.Matmul.eq.SumMulDataS.of.Lt
import Lemma.Tensor.SEqDataS.of.SEq
import Lemma.Tensor.Select_0.eq.Cast_Get.of.GtLength_0
import Lemma.Vector.Cast_Cast.eq.Cast.of.Eq.Eq
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.EqSumS.of.SEq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetFlatten_AddMul.eq.Get.of.Lt.Lt.Eq
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.Repeat.eq.Cast.of.Eq_1
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin List Nat Tensor Vector
set_option maxHeartbeats 2000000


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
  rw [Matmul.eq.Cast_BroadcastMatmul.of.LtGetS_SubLength.GeLength_2.GeLength_2 (by simp) (by simp) (by simpa)]
  simp
  rw [Matmul.eq.SelectBatchDot.of.Lt_Get_SubLength.GeLength_2 (by simp) (by simpa)]
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
  unfold broadcast
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
  rw [DataCast.eq.Cast_Data.of.Eq (by simp [EqAddMulDiv])]
  simp [XiAppend, Xi, X']
  rw [Repeat.eq.Cast.of.Eq_1 (by rw [EqDivMul.of.Ne_0 (by omega)])]
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


@[main, fin]
private lemma one
  [NonUnitalNonAssocSemiring α]
-- given
  (h : k < n')
  (X : Tensor α [n, k])
  (Y : Tensor α [n'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by simp) X Y i) = X[i] @ Y := by
-- proof
  simp [GetElem.getElem]
  simp [MatMul.dot]
  rw [Matmul.eq.Cast_SelectBatchDot.of.LtGet_SubLength_1.GeLength_2]
  ·
    simp [Matmul.eq.SumMulDataS.of.Lt h]
    unfold Tensor.broadcast
    unfold Tensor.batch_dot
    simp
    have h_nk : n' / k * k + n' % k = n' := by simp [EqAddMulDiv]
    have h_s0 : [] ++ [n] ++ [n' / k * k + n' % k] = [] ++ [n, n'] := by
      simpa
    have h_s1 : ([] ++ [1, 1, n']).set ([] : List ℕ).length (n * ([] ++ [1, 1, n'])[([] : List ℕ).length]) = [] ++ [n, 1, n'] := by
      simp
    have h_s2 : [n', 1].prod / [n'].prod * [n'].prod = [n', 1].prod := by
      simp [Nat.EqMulDiv]
    let X' : Tensor α ([n] ++ [n' / k * k]) := X.repeat (n' / k) (1 : Fin 2)
    let X'Append : Tensor α ([n] ++ [n' / k * k + n' % k]) := X' ++ (0 : Tensor α ([n] ++ [n' % k]))
    let X'Repeat : Tensor α ([] ++ [n, 1, n']) := ((cast (congrArg (Tensor α) h_s0) X'Append).unsqueeze 1).repeat 1 (1 : Fin 3)
    have := GetSelect_1.eq.Cast_Get.of.Lt_Get_0.Lt_Get_1.GtLength_1
      (by grind)
      (by grind)
      (by grind)
      ((X'Repeat * cast (congrArg (Tensor α) h_s1)
        (((⟨cast (congrArg (List.Vector α) h_s2)
          (Y.data.repeat (n' * 1 / (n' * 1)))⟩ : Tensor α _)ᵀ.unsqueeze 0).repeat n (0 : Fin 3))).sum 2
      )
      (i := 0) (j := i)
    simp at this
    rw [this]
    rw [GetSum_2.eq.SumGet__0.fin]
    rw [@Tensor.GetMul.eq.MulGetS.fin]
    have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
      (by grind)
      (by
        simp
        constructor
        ·
          simp only [GetElem.getElem]
          simp
        ·
          rfl
      )
      (((⟨cast (congrArg (List.Vector α) h_s2) (Y.data.repeat (n' * 1 / (n' * 1)))⟩ : Tensor α _)ᵀ.unsqueeze 0).repeat n (0 : Fin 3))
      ⟨i, by grind⟩
      (s' := [n, 1, n'])
    simp at this
    rw [this]
    apply Eq.of.EqDataS
    simp
    rw [Repeat.eq.Cast.of.Eq_1]
    ·
      rw [Cast_Cast.eq.Cast.of.Eq.Eq]
      ·
        unfold Tensor.unsqueeze
        simp
        unfold Tensor.repeat
        simp
        apply @Vector.Eq.of.All_EqGetS.fin
        intro t
        have h_t := Eq_0 t
        subst h_t
        simp [@Tensor.GetMul.eq.MulGetS.fin]
        conv_rhs => simp [List.Vector.head]
        rw [DataCast.eq.Cast_Data.of.Eq (by simp_all)]
        rw [DataAppend.eq.Cast_AppendDataS]
        simp [X'Repeat, X'Append, X']
        rw [EqData0'0]
        unfold Tensor.unsqueeze
        simp
        unfold Tensor.repeat
        simp
        rw [HeadDataSum.eq.SumData]
        apply EqSumS.of.SEq
        apply SEq.of.All_EqGetS.Eq.fin
        ·
          intro j
          have h_j := j.isLt
          simp at h_j
          simp [@Vector.GetMul.eq.MulGetS.fin]
          rw [GetCast.eq.Get.of.Eq.fin (by simpa)]
          rw [DataMul.eq.MulDataS]
          simp [@Vector.GetMul.eq.MulGetS.fin]
          rw [DataGet.eq.GetUnflattenData.fin]
          rw [GetUnflatten.eq.Get_AddMul.fin]
          simp
          rw [DataGet.eq.GetUnflattenData.fin]
          rw [GetUnflatten.eq.Get_AddMul.fin]
          simp
          rw [GetCast.eq.Get.of.Eq.fin (by simp)]
          simp
          rw [GetFlatten_AddMul.eq.Get.of.Lt.Lt.Eq.fin (by simp) (by simp) (by simpa)]
          simp [GetRepeat.eq.Get_Mod.fin]
          simp [EqMod.of.Lt h_j]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp
          rw [GetCast.eq.Get.of.Eq.fin (by simp)]

          simp
          repeat rw [DataGet.eq.GetUnflattenData.fin]
          repeat rw [GetUnflatten.eq.Get_AddMul.fin]
          simp
          rw [GetCast.eq.Get.of.Eq.fin]
          ·
            simp
            have h_lt : ↑i * n' + ↑j < 1 * (n * (1 * ([n', 1].swap 0 1).prod)) := by
              simp [ProdSwap.eq.Prod]
              apply AddMul.lt.Mul.of.Lt.Lt i.isLt h_j
            obtain ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
            simp
            rw [GetRepeat.eq.Get_Mod.fin]
            simp [ProdSwap.eq.Prod]
            rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            simp
            rw [DataTransposeTensor.eq.Cast]
            simp
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
              simp [ProdSwap.eq.Prod] at h_r_mod
              simp [h_r_mod]
              simp [EqMod.of.Lt h_j]
              apply EqMulS.of.Eq
              rw [DataCast.eq.Cast_Data.of.Eq (by simpa)]
              rw [GetCast.eq.Get.of.Eq.fin (by grind)]
              simp
              have h_s2 : ([n, k].take ↑1).prod * (n' / k * ([n, k].drop ↑1).prod) = ([n, k].set (↑1) (n' / k * [n, k][↑1])).prod := by
                simp
              have A : Tensor α ([n] ++ (n' / k * k):: []) := ⟨cast (congrArg (List.Vector α) h_s2) ((X.data.splitAt 1).map fun x ↦ x.repeat (n' / k)).flatten⟩
              have := DataAppend.eq.Cast_AppendDataS A (0 : Tensor α ([n] ++ (n' % k) :: []))
              simp at this
              rw [this]
              sorry
            ·
              simp [ProdSwap.eq.Prod]
          ·
            simp [ProdSwap.eq.Prod]
            left
            grind
        ·
          simp
      ·
        grind
      ·
        grind
    ·
      simp
      rw [Div.eq.One.of.Ne_0]
      grind
  ·
    simp
  ·
    simpa


-- created on 2026-01-10
-- updated on 2026-04-25
