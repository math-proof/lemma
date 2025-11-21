import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.DropSet.eq.Drop.of.Lt
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Lt
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.Lt_Length
import Lemma.List.GetSet.eq.Get.of.Lt.Lt_Length
import Lemma.List.GetTake.eq.Get.of.Lt_LengthTake
import Lemma.List.LengthSet.eq.Length
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.Lt_Length
import Lemma.List.ProdSet__Mul_Get.eq.Mul_Prod.of.Lt_Length
import Lemma.List.ProdTake.eq.MulProdTake.of.Lt_Length
import Lemma.List.TakeSet.eq.SetTake.of.Lt
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Lt.of.Lt.Lt
import Lemma.Nat.Mul
import Lemma.Nat.MulMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataRepeat.eq.Cast_FlattenMapSplitAtData
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Nat Tensor Vector


@[main]
private lemma main
-- given
  (h_d : d < s.length)
  (h_i : i < s[d])
  (h_k : k < d)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.repeat n ⟨k, by grind⟩).select ⟨d, by grind⟩ ⟨i, by grind⟩ ≃ (X.select ⟨d, by grind⟩ ⟨i, by grind⟩).repeat n ⟨k, by grind⟩ := by
-- proof
  apply SEq.of.SEqDataS.Eq
  ·
    simp
    rw [GetEraseIdx.eq.Get.of.Lt.Lt_Length h_d h_k]
    grind
  ·
    rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0]
    conv_rhs => rw [DataRepeat.eq.Cast_FlattenMapSplitAtData]
    have h_k_length : k < (s.eraseIdx d).length := by grind
    have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (s := s.set k (n * s[k])) (d := d) (i := i) (by grind) (by grind)
    simp at h_length_slice
    have h_prod_set := ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.Lt_Length h_k_length n
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp [← h_length_slice]
    ·
      simp [h_prod_set]
    ·
      rw [GetEraseIdx.eq.Get.of.Lt.Lt_Length h_d h_k] at h_prod_set
      simp [List.Vector.length]
      apply SEq.of.All_EqGetS.Eq.fin
      ·
        intro t
        have h_t := t.isLt
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        have h_q := q.isLt
        have h_r := r.isLt
        have h_d_lt_length := LengthSet.eq.Length s k (n * s[k]) ▸ h_d
        have := LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (i := i) h_d_lt_length (by grind)
        simp at this
        simp [this] at h_q
        let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        simp [h_length_slice] at h_t
        rw [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k] at h_t
        rw [h_prod_set] at h_t
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
        simp
        rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin]
        ·
          rw [GetRepeat.eq.Get_Mod.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp [GetSet.eq.Get.of.Lt.Lt_Length h_d h_k]
          simp [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0]
          simp [DataRepeat.eq.Cast_FlattenMapSplitAtData]
          have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (s := s) (d := d) (i := i) (by grind) (by grind)
          repeat rw [GetCast.eq.Get.of.Eq.fin]
          ·
            simp [List.Vector.length]
            have h_lt : (↑q * s[d] + i) * ((s.set k (n * s[k])).drop (d + 1)).prod + ↑r < (s.take k).prod * (n * (s.drop k).prod) := by
              simp [DropSet.eq.Drop.of.Lt (show k < d + 1 by omega)] at ⊢ h_r
              rw [Mul_Mul.eq.MulMul]
              rw [MulMul.comm]
              simp
              rw [Mul.comm (b := n)]
              simp only [Prod.eq.MulProdS s (d + 1)]
              rw [Mul_Mul.eq.MulMul]
              apply AddMul.lt.Mul.of.Lt.Lt _ h_r
              rw [ProdTake.eq.MulProdTake.of.Lt_Length h_d]
              rw [Mul_Mul.eq.MulMul]
              apply AddMul.lt.Mul.of.Lt.Lt _ h_i
              rw [TakeSet.eq.SetTake.of.Lt h_k] at h_q
              have := ProdSet__Mul_Get.eq.Mul_Prod.of.Lt_Length (s := (s.take d)) (i := k) (by simp; grind) n
              rw [GetTake.eq.Get.of.Lt_LengthTake (by grind)] at this
              rwa [this] at h_q
            let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
            let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
            have h_lt : ↑q' * ((s.eraseIdx d).drop k).prod + ↑r' % ((s.eraseIdx d).drop k).prod < (⟨↑i, ↑(s.take (d + 1)).prod, ↑s[d]⟩ : Slice).length (s.take (d + 1)).prod * (s.drop (d + 1)).prod := by
              simp [h_length_slice]
              rw [Prod.eq.MulProdS (s.eraseIdx d) k]
              apply AddMul.lt.Mul.of.Lt.Lt q'.isLt
              apply LtMod.of.Gt_0
              grind
            let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
            have h_qₑ := qₑ.isLt
            have := LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (s := s) (d := d) (i := i) (by grind) (by grind)
            simp at this
            simp [this] at h_qₑ
            let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
            repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
            rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin _ _ h_i]
            ·
              simp
              rw [GetRepeat.eq.Get_Mod.fin]
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              apply congrArg
              simp
              sorry
            ·
              simp [ProdTake.eq.MulProdTake.of.Lt_Length h_d]
            ·
              simp [ProdTake.eq.MulProdTake.of.Lt_Length h_d]
              rwa [EqDivMul.of.Ne_0 (by grind)]
          ·
            simp [h_length_slice]
          ·
            simp [ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.Lt_Length (Lt.of.Lt.Lt h_k h_d)]
        ·
          simp [ProdTake.eq.MulProdTake.of.Lt_Length h_d_lt_length]
        ·
          simp [ProdTake.eq.MulProdTake.of.Lt_Length h_d_lt_length]
          rwa [EqDivMul.of.Ne_0 (by grind)]
        ·
          rwa [GetSet.eq.Get.of.Lt.Lt_Length h_d h_k]
      ·
        simp
        rw [h_length_slice]
        rw [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k]
        rw [h_prod_set]


-- created on 2025-11-18
