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
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Cast.eq.Fin.of.Lt.Eq
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
import Lemma.Vector.GetGetSlice.eq.Get.of.GtGet.GtLength
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat Bool List Tensor Vector Finset Fin


@[main]
private lemma main
  {d : Fin s.length}
  {k : ℕ}
-- given
  (h_k : k ≤ d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  have h_k_lt : k < d + 1 := by omega
  have h_d := d.isLt
  (X.unsqueeze k).select ⟨d + 1, by grind⟩ ⟨i, by simp [GetInsertIdx.eq.Get.of.Lt.GeLength h_d h_k_lt]⟩ ≃ (X.select d i).unsqueeze k := by
-- proof
  intro h_k_lt h_d
  have h_i := i.isLt
  apply SEq.of.SEqDataS.Eq
  ·
    apply EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength (by omega) h_k_lt
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
          let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
          let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
          have h_q := q.isLt
          simp at h_q
          have h_r := r.isLt
          rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
          simp at h_t
          rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (by grind) (by grind)] at h_t
          rw [EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength (by omega) h_k_lt] at h_t
          rw [ProdInsertIdx.eq.Prod] at h_t
          have h_lt : t < (⟨i, (s.take (d + 1)).prod, s[d]⟩ : Slice).length (s.take (d + 1)).prod * (s.drop (d + 1)).prod := by
            simp
            have := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength.simp (by omega) h_i
            simp at this
            rwa [this]
          let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
          let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
          have h_q' := q'.isLt
          have h_r' := r'.isLt
          rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := q') (j := r')]
          ·
            repeat rw [GetGetSlice.eq.Get.of.GtGet.GtLength (by grind) (by grind)]
            repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            simp [DataUnsqueeze.eq.Map_FunGetData.fin]
            apply congrArg
            rw [Cast.eq.Fin.of.Lt.Eq]
            ·
              simp [EqGetRange.fin]
              simp [DropInsertIdx.eq.Drop.of.Lt (show k < d + 1 + 1 by omega)] at ⊢ h_q_div h_r_mod
              simp [← h_q_div] at h_q'_div
              simp [← h_r_mod] at h_r'_mod
              simp [h_q'_div, h_r'_mod]
              simp [GetInsertIdx.eq.Get.of.Lt.GeLength h_d h_k_lt]
            ·
              rw [ProdInsertIdx.eq.Prod]
            ·
              simp [EqGetRange.fin]
              simp [DropInsertIdx.eq.Drop.of.Lt (show k < d + 1 + 1 by omega)] at ⊢ h_r
              rw [Prod.eq.MulProdS s (d + 1)]
              apply AddMul.lt.Mul.of.Lt.Lt _ h_r
              simp [GetInsertIdx.eq.Get.of.Lt.GeLength h_d h_k_lt]
              apply AddMul.lt.Mul.of.Lt.Lt _ h_i
              rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (by grind) (by grind)] at h_q
              rw [TakeInsertIdx.eq.InsertIdxTake.of.Lt.GeLength (show s.length ≥ k by omega) h_k_lt] at h_q
              rwa [ProdInsertIdx.eq.Prod] at h_q
          ·
            rw [← h_q'r']
            apply EqValCast.of.Lt.Eq _ h_t
            simp [ProdInsertIdx.eq.Prod]
        ·
          simp
          have := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength h_d h_i
          simp at this
          simp [this]
      ·
        simp
        rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength _ (by grind)]
        rw [EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength (by omega) h_k_lt]
        grind


-- created on 2025-11-26
-- updated on 2025-11-27
