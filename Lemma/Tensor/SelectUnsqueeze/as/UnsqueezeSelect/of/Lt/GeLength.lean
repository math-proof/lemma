import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Finset.Prod.eq.MulProdS
import Lemma.List.DropInsertIdx.eq.Drop.of.Lt
import Lemma.List.EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength
import Lemma.List.GetInsertIdx.eq.Get.of.Lt.GeLength
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.List.TakeInsertIdx.eq.InsertIdxTake.of.Lt.GeLength
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Cast.eq.Mk.of.Lt.Eq
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqValCast.of.Lt.Eq
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.DataUnsqueeze.eq.Map_FunGetData
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.EqGetRange
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat Bool List Tensor Vector Finset


@[main]
private lemma main
-- given
  (h_d : s.length ≥ d)
  (h_k : k < d)
  (X : Tensor α s)
  (i : Fin s[d - 1]) :
-- imply
  (X.unsqueeze k).select ⟨d, by grind⟩ ⟨i, by simp [GetInsertIdx.eq.Get.of.Lt.GeLength h_d h_k]⟩ ≃ (X.select ⟨d - 1, by omega⟩ ⟨i, i.isLt⟩).unsqueeze k := by
-- proof
  apply SEq.of.SEqDataS.Eq
  ·
    apply EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength (by omega) h_k
  ·
    simp
    rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData]
    apply SEqCast.of.SEq.Eq
    ·
      simp
      rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
      grind
    ·
      simp
      conv_rhs => rw [DataUnsqueeze.eq.Map_FunGetData.fin]
      apply SEq.of.All_EqGetS.Eq.fin
      ·
        intro t
        have h_t := t.isLt
        simp [EqGetRange.fin]
        rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData]
        rw [GetCast.eq.Get.of.Eq.fin]
        ·
          simp [List.Vector.length]
          let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
          let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
          have h_q := q.isLt
          simp at h_q
          have h_r := r.isLt
          rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
          simp at h_t
          rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (by grind) (by grind)] at h_t
          rw [EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength (by omega) h_k] at h_t
          rw [ProdInsertIdx.eq.Prod] at h_t
          have h_lt : t < (⟨i, (s.take (d - 1 + 1)).prod, s[d - 1]⟩ : Slice).length (s.take (d - 1 + 1)).prod * (s.drop (d - 1 + 1)).prod := by 
            simp
            rwa [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (by omega) i.isLt]
          let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
          let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
          have h_q' := q'.isLt
          have h_r' := r'.isLt
          rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := q') (j := r')]
          ·
            repeat rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin]
            ·
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              simp [DataUnsqueeze.eq.Map_FunGetData.fin]
              apply congrArg
              rw [Cast.eq.Mk.of.Lt.Eq]
              ·
                simp [EqGetRange.fin]
                simp [DropInsertIdx.eq.Drop.of.Lt (show k < d + 1 by omega)] at ⊢ h_q_div h_r_mod
                simp [EqAddSub.of.Ge (show d ≥ 1 by omega)] at ⊢ h_q'_div h_r'_mod
                simp [← h_q_div] at h_q'_div
                simp [← h_r_mod] at h_r'_mod
                simp [h_q'_div, h_r'_mod]
                simp [GetInsertIdx.eq.Get.of.Lt.GeLength h_d h_k]
              ·
                rw [ProdInsertIdx.eq.Prod]
              ·
                simp [EqGetRange.fin]
                simp [DropInsertIdx.eq.Drop.of.Lt (show k < d + 1 by omega)] at ⊢ h_r
                rw [Prod.eq.MulProdS s d]
                apply AddMul.lt.Mul.of.Lt.Lt _ h_r
                simp [GetInsertIdx.eq.Get.of.Lt.GeLength h_d h_k]
                have := ProdTake.eq.MulProdTake.of.GtLength (show d - 1 < s.length by omega)
                rw [EqAddSub.of.Ge (by omega)] at this
                rw [this]
                apply AddMul.lt.Mul.of.Lt.Lt _ i.isLt
                rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (by grind) (by grind)] at h_q
                rw [TakeInsertIdx.eq.InsertIdxTake.of.Lt.GeLength (show s.length ≥ k by omega) h_k] at h_q
                rwa [ProdInsertIdx.eq.Prod] at h_q
            ·
              simp [ProdTake.eq.MulProdTake.of.GtLength (show d - 1 < s.length by omega)]
            ·
              simp [ProdTake.eq.MulProdTake.of.GtLength (show d - 1 < s.length by omega)]
              rw [EqDivMul.of.Ne_0]
              ·
                simp at h_q'
                rwa [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (by grind) (by grind)] at h_q'
              ·
                linarith [i.isLt]
            ·
              grind
            ·
              simp [ProdTake.eq.MulProdTake.of.GtLength (show d < (s.insertIdx k 1).length by grind)]
            ·
              simp [ProdTake.eq.MulProdTake.of.GtLength (show d < (s.insertIdx k 1).length by grind)]
              rw [EqDivMul.of.Ne_0]
              ·
                rwa [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (by grind) (by grind)] at h_q
              ·
                rw [GetInsertIdx.eq.Get.of.Lt.GeLength (by omega) (by omega)]
                linarith [i.isLt]
            ·
              grind
          ·
            rw [← h_q'r']
            apply EqValCast.of.Lt.Eq _ h_t
            rw [ProdInsertIdx.eq.Prod]
        ·
          simp
          rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
          grind
      ·
        simp
        rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
        rw [EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength (by omega) h_k]
        grind


-- created on 2025-11-26
-- updated on 2025-11-27
