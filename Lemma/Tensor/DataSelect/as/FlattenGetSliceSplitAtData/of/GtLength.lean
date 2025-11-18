import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Int.EqSubAdd
import Lemma.List.DropTail.eq.Drop
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.EqLengthSlice_CoeMul.of.Lt
import Lemma.List.EqLengthSlice_Mul.of.Lt
import Lemma.List.EraseIdxCons.eq.EraseIdx_Sub_1.of.Gt_0
import Lemma.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
import Lemma.List.LengthSlice.eq.One.of.Lt
import Lemma.List.MapCast.eq.Cast_Map.of.Eq
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.List.ProdCons.eq.Mul_Prod
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.List.ProdEraseIdx.eq.Mul_ProdEraseIdxTail.of.GtLength_0
import Lemma.List.ProdTail.eq.MulProdS
import Lemma.List.ProdTake.eq.MulProdTake.of.Lt_Length
import Lemma.List.ProdTake.eq.Mul_ProdTake.of.Lt_Length
import Lemma.List.ProdTakeTailMapCast.eq.CastProdTakeTail
import Lemma.List.TailTake.eq.TakeTail
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqSubAdd
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataGet.as.GetSplitAtData.of.GtLength_0
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.DataStack.eq.FlattenMap_FunData
import Lemma.Tensor.Lt_Length.of.GtLength_0
import Lemma.Tensor.SEqStack_Get.of.GtLength_0
import Lemma.Tensor.SelectCast.eq.Cast_Select.of.Eq
import Lemma.Tensor.SelectStack.eq.Stack_Select.of.GtLength
import Lemma.Tensor.Select_0.eq.Cast_Get.of.GtLength_0
import Lemma.Vector.EqGetRange
import Lemma.Vector.FlattenCast.eq.Cast_Flatten.of.Eq.Eq
import Lemma.Vector.FlattenMapRange.eq.Cast_UFn_0
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
import Lemma.Vector.Indices.eq.Cast_MapRange
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat Bool Int List Tensor Vector
set_option maxHeartbeats 2000000


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.select ⟨d, h⟩ i).data ≃ (X.data.splitAt (d + 1))[i :: s[d]].flatten := by
-- proof
  simp
  induction d generalizing s X with
  | zero =>
    simp
    match s with
    | [] =>
      contradiction
    | s₀ :: s =>
      rw [Select_0.eq.Cast_Get.of.GtLength_0]
      rw [DataCast.eq.Cast_Data.of.Eq (by simp)]
      simp only [List.Vector.length]
      apply SEqCast.of.SEq.Eq.Eq (by simp)
      ·
        simp [LengthSlice.eq.One.of.Lt]
      ·
        have := DataGet.as.GetSplitAtData.of.GtLength_0.fin h X i
        apply SEq.trans this
        unfold List.Vector.getSlice
        simp [List.Vector.length]
        simp [GetElem.getElem]
        rw [GetSplitAt_1.eq.GetUnflatten.fin]
        have h_i := i.isLt
        conv_rhs at h_i => simp
        have := Indices.eq.Cast_MapRange.comm ⟨i, h_i⟩ 1
        simp at this
        rw [this]
        rw [MapCast.eq.Cast_Map.of.Eq]
        ·
          simp
          rw [FlattenCast.eq.Cast_Flatten.of.Eq.Eq]
          ·
            apply SEq_Cast.of.SEq.Eq.Eq
            ·
              simp [LengthSlice.eq.One.of.Lt]
            ·
              simp [LengthSlice.eq.One.of.Lt]
            ·
              rw [FlattenMapRange.eq.Cast_UFn_0]
              apply SEq_Cast.of.SEq.Eq.Eq
              ·
                simp
              ·
                simp
              ·
                rw [GetSplitAt_1.eq.GetUnflatten.fin]
          ·
            simp [LengthSlice.eq.One.of.Lt]
          ·
            rfl
        ·
          simp [LengthSlice.eq.One.of.Lt]
  | succ d ih =>
    have h_X := SEqStack_Get.of.GtLength_0 (by omega) X
    have h_X := EqCast.of.SEq h_X
    conv_lhs => rw [← h_X]
    have h_s := EqCons_Tail.of.GtLength_0 (s := s) (by omega)
    have := SelectCast.eq.Cast_Select.of.Eq h_s (([i < s[0]] (X[i]'(Lt_Length.of.GtLength_0 (by omega) X i)))) ⟨d + 1, by simp; grind⟩ ⟨i, by grind⟩
    simp at this
    simp [this]
    rw [DataCast.eq.Cast_Data.of.Eq (by grind)]
    apply SEqCast.of.SEq.Eq.Eq (by grind)
    ·
      simp [List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
    ·
      have h_d_lt_sub := GtSub.of.Gt_Add h
      apply SEq.of.All_EqGetS.Eq
      ·
        intro t
        have h_t := t.isLt
        rw [SelectStack.eq.Stack_Select.of.GtLength]
        have ih := ih (s := s.tail) (by simpa) (i := ⟨i, by simp⟩)
        simp at ih
        have h_eq : (⟨i, ((List.map Nat.cast s).tail.take (d + 1)).prod, s[d + 1]⟩ : Slice).length (s.tail.take (d + 1)).prod * (s.drop (d + 1 + 1)).prod = (s.tail.eraseIdx d).prod := by
          rw [ProdTakeTailMapCast.eq.CastProdTakeTail]
          rw [ProdTake.eq.MulProdTake.of.Lt_Length (by grind)]
          rw [GetTail.eq.Get_Add_1.of.Lt_SubLength_1 (by omega)]
          rw [EqLengthSlice_CoeMul.of.Lt (by omega)]
          rw [Drop.eq.DropTail]
          rw [ProdEraseIdx.eq.MulProdS]
        have h_all : ∀ (X : Tensor α s.tail), (X.select ⟨d, by grind⟩ ⟨i, by grind⟩).data = cast
          (by
            simp
            rw [GetTail.eq.Get_Add_1.of.Lt_SubLength_1 (by omega)]
            simp only [h_eq]
          )
          ((X.data.splitAt (d + 1)).getSlice ⟨i, (X.data.splitAt (d + 1)).length, s.tail[d]'(by simpa)⟩).flatten := by
            intro X
            apply Eq_Cast.of.SEq
            apply ih
        rw [DataStack.eq.FlattenMap_FunData.fin]
        simp [h_all]
        simp only [EraseIdxCons.eq.EraseIdx_Sub_1.of.Gt_0 (show d + 1 > 0 by omega)] at h_t
        rw [@Nat.EqSubAdd] at h_t
        rw [ProdCons.eq.Mul_Prod] at h_t
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        rw [Mul_ProdEraseIdxTail.eq.ProdEraseIdx.of.GtLength_0] at h_t
        have h_t : t < (⟨i, (X.data.splitAt (d + 1 + 1)).length, s[d + 1]⟩ : Slice).length (s.take (d + 1 + 1)).prod * (s.drop (d + 1 + 1)).prod := by
          simpa [List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
        simp only [GetElem.getElem]
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
        simp
        rw [GetCast.eq.Get.of.Eq.fin (by simp [h_eq])]
        rw [EqGetRange.fin]
        simp [List.Vector.length]
        have h_d_lt : d < s.tail.length := by grind
        have h_r := r.isLt
        have h_lt : r < (⟨i, (s.tail.take (d + 1)).prod, s.tail[d]'(by simpa)⟩ : Slice).length (s.tail.take (d + 1)).prod * (s.tail.drop (d + 1)).prod := by
          simp
          rw [ProdTakeTailMapCast.eq.CastProdTakeTail]
          rw [ProdTake.eq.MulProdTake.of.Lt_Length h_d_lt]
          rw [GetTail.eq.Get_Add_1.of.Lt_SubLength_1 h_d_lt_sub]
          rw [EqLengthSlice_CoeMul.of.Lt (by omega)]
          rw [Drop.eq.DropTail]
          rwa [MulProdS.eq.ProdEraseIdx]
        let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
        let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
        repeat rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin]
        ·
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin]
          rw [GetCast.eq.Get.of.Eq.fin (by simp)]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          apply congrArg
          simp
          repeat rw [MulAdd.eq.AddMulS]
          conv_lhs => rw [AddAdd.comm]
          conv_rhs => rw [AddAdd.comm]
          simp [Add_Add.eq.AddAdd]
          simp at h_qₐ_div h_rₐ_mod h_r'_mod
          simp [h_qₐ_div, h_rₐ_mod]
          simp [ProdEraseIdx.eq.MulProdS] at h_r_mod
          conv_lhs =>
            arg 2
            simp [h_r_mod]
          simp [← h_r'_mod]
          rw [ProdTail.eq.MulProdS s (d + 1)]
          rw [Mul_Mul.eq.MulMul]
          simp [AddMulS.eq.MulAdd]
          left
          rw [ProdTake.eq.Mul_ProdTake.of.Lt_Length (by omega)]
          rw [GetTail.eq.Get_Add_1.of.Lt_SubLength_1 h_d_lt_sub]
          rw [Mul_Mul.eq.MulMul]
          rw [MulMul.comm]
          simp [AddMulS.eq.MulAdd]
          left
          simp [h_q'_div, h_qr]
          simp [ProdEraseIdx.eq.MulProdS]
          rw [Mul_Mul.eq.MulMul]
          rw [DivAddMul.eq.Add_Div.of.Gt_0]
          have h_rₐ := rₐ.isLt
          simp at h_rₐ
          omega
        ·
          simp [ProdTake.eq.MulProdTake.of.Lt_Length h]
        ·
          simp [ProdTake.eq.MulProdTake.of.Lt_Length h]
          rw [EqDivMul.of.Ne_0 (by grind)]
          have h_q' := q'.isLt
          simp at h_q'
          rwa [List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength h (by omega)] at h_q'
        ·
          grind
        ·
          simp [ProdTake.eq.MulProdTake.of.Lt_Length h_d_lt]
        ·
          simp [ProdTake.eq.MulProdTake.of.Lt_Length h_d_lt]
          rw [EqDivMul.of.Ne_0 (by grind)]
          convert (qₐ.isLt)
          simp
          rw [ProdTakeTailMapCast.eq.CastProdTakeTail]
          rw [ProdTake.eq.MulProdTake.of.Lt_Length h_d_lt]
          rw [GetTail.eq.Get_Add_1.of.Lt_SubLength_1 h_d_lt_sub]
          rw [EqLengthSlice_CoeMul.of.Lt (by omega)]
        ·
          grind
      ·
        simp [List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
        rw [List.ProdEraseIdx.eq.Mul_ProdEraseIdxTail.of.GtLength_0]


-- created on 2025-11-10
-- updated on 2025-11-14
