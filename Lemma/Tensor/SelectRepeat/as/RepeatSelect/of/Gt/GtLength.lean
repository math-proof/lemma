import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Finset.Prod.eq.MulProdS
import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.List.DvdMulS_ProdDrop.of.Ge
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Gt
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.GtLength
import Lemma.List.GetSet.eq.Get.of.Gt.GtLength
import Lemma.List.LengthSet.eq.Length
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.ProdDrop.eq.MulProdSDrop.of.Le
import Lemma.List.ProdDropSet__Mul_Get.eq.Mul_ProdDrop.of.Ge.GtLength
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.List.ProdTakeMapCast.eq.CastProdTake
import Lemma.List.TakeSet.eq.Take.of.Gt
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.DivMod_Mul.eq.ModDiv
import Lemma.Nat.Dvd_Mul.of.Dvd
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Le.of.Lt
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.ModAdd.eq.Mod.of.Dvd
import Lemma.Nat.Mod_Mul.eq.AddMul_Mod.of.Ne_0
import Lemma.Nat.Mul
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Mul_Mul
import Lemma.Tensor.DataRepeat.eq.Cast_FlattenMapSplitAtData
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Finset List Nat Tensor Vector


@[main]
private lemma main
  {d k : ℕ}
-- given
  (h_k : s.length > k)
  (h_d : k > d)
  (X : Tensor α s)
  (i : Fin s[d])
  (n : ℕ) :
-- imply
  (X.repeat n ⟨k, h_k⟩).select ⟨d, by grind⟩ ⟨i, by grind⟩ ≃ (X.select ⟨d, by grind⟩ i).repeat n ⟨k - 1, by grind⟩ := by
-- proof
  have h_i := i.isLt
  have h_d_length := h_d.trans h_k
  have h_get_eraseIdx := GetEraseIdx.eq.Get.of.Lt.GtLength h_k h_d
  apply SEq.of.SEqDataS.Eq
  ·
    simp [h_get_eraseIdx]
    grind
  ·
    rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
    conv_rhs => rw [DataRepeat.eq.Cast_FlattenMapSplitAtData]
    have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (s := s.set k (n * s[k])) (d := d) (i := i) (by grind) (by grind)
    rw [ProdTakeMapCast.eq.CastProdTake] at h_length_slice
    simp at h_length_slice
    have h_prod_set := ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength (s := s.eraseIdx d) (i := k - 1) (by grind) n
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp [← h_length_slice]
    ·
      simp [h_prod_set]
    ·
      rw [h_get_eraseIdx] at h_prod_set
      simp
      apply SEq.of.All_EqGetS.Eq.fin
      ·
        intro t
        have h_t := t.isLt
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        have h_q := q.isLt
        have h_r := r.isLt
        have h_s := LengthSet.eq.Length s k (n * s[k])
        have h_d_lt_length := h_d_length
        simp only [← h_s] at h_d_lt_length
        have := LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (i := i) h_d_lt_length (show ↑i < (s.set k (n * s[k]))[d] by grind)
        rw [ProdTakeMapCast.eq.CastProdTake] at this
        simp only [this] at h_q
        let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        simp [h_length_slice] at h_t
        rw [EraseIdxSet.eq.SetEraseIdx.of.Gt h_d] at h_t
        rw [h_prod_set] at h_t
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
        simp
        rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin]
        ·
          rw [GetRepeat.eq.Get_Mod.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp [GetSet.eq.Get.of.Gt.GtLength h_d_length h_d]
          rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
          simp [DataRepeat.eq.Cast_FlattenMapSplitAtData]
          have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (s := s) (d := d) (i := i) (by grind) (by grind)
          rw [ProdTakeMapCast.eq.CastProdTake] at h_length_slice
          repeat rw [GetCast.eq.Get.of.Eq.fin]
          ·
            have h_prod_take := ProdTake.eq.MulProdTake.of.GtLength h_d_length
            have h_lt : (↑q * s[d] + i) * ((s.set k (n * s[k])).drop (d + 1)).prod + ↑r < (s.take k).prod * (n * (s.drop k).prod) := by
              simp [ProdDropSet__Mul_Get.eq.Mul_ProdDrop.of.Ge.GtLength h_k h_d] at ⊢ h_r
              conv_rhs =>
                simp [Mul.comm (a := n)]
                rw [Mul_Mul.eq.MulMul]
              simp
              simp only [Prod.eq.MulProdS s (d + 1)]
              rw [MulMul.comm]
              rw [MulMul.eq.Mul_Mul]
              apply AddMul.lt.Mul.of.Lt.Lt _ h_r
              rw [h_prod_take]
              rw [TakeSet.eq.Take.of.Gt h_d] at h_q
              apply AddMul.lt.Mul.of.Lt.Lt h_q h_i
            let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
            let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
            have h_lt : ↑q' * ((s.eraseIdx d).drop (k - 1)).prod + ↑r' % ((s.eraseIdx d).drop (k - 1)).prod < (⟨↑i, ↑(s.take (d + 1)).prod, s[d]⟩ : Slice).length (s.take (d + 1)).prod * (s.drop (d + 1)).prod := by
              rw [h_length_slice]
              rw [Prod.eq.MulProdS (s.eraseIdx d) (k - 1)]
              apply AddMul.lt.Mul.of.Lt.Lt q'.isLt
              apply LtMod.of.Gt_0
              grind
            let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
            have h_qₐ := qₐ.isLt
            let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
            repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
            rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin _ _ (by assumption)]
            ·
              simp [GetRepeat.eq.Get_Mod.fin]
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              apply congrArg
              simp
              have h_d' := Le.of.Lt h_d
              simp [ProdDropSet__Mul_Get.eq.Mul_ProdDrop.of.Ge.GtLength h_k h_d] at h_qₑ_div h_rₑ_mod h_q_div h_r_mod h_r
              rw [ModAdd.eq.Mod.of.Dvd.left (Dvd_Mul.of.Dvd (DvdMulS_ProdDrop.of.Ge h_d s n) (↑q * s[d] + ↑i))] at h_rₑ_mod
              rw [ProdDrop.eq.MulProdSDrop.of.Le (show d + 1 ≤ k by omega) s] at h_qₑ_div
              simp [h_rₑ_mod]
              rw [Mul_Mul.comm (a := n), Mul_Mul.eq.MulMul] at h_qₑ_div
              simp [DropEraseIdx.eq.Drop.of.Le (show d ≤ k - 1 by omega)] at h_qₐ_div h_rₐ_mod h_q'_div h_r'_mod
              rw [EqAddSub.of.Ge (show k ≥ 1 by omega)] at h_qₐ_div h_rₐ_mod h_q'_div h_r'_mod
              simp [ProdDrop.eq.MulProdSDrop.of.Le (show d + 1 ≤ k by omega) s] at h_qₐ_div h_rₐ_mod
              rw [Div_Mul.eq.DivDiv.comm] at h_qₐ_div
              rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₐ_div h_qₑ_div
              rw [Mod_Mul.eq.AddMul_Mod.of.Ne_0 (by grind)] at h_rₐ_mod
              simp at h_qₐ_div
              have h_prod_drop := ProdDrop.eq.MulProdSDrop.of.Le (i := d + 1) (j := k) (by omega) s
              simp [h_qₐ_div, h_rₐ_mod]
              simp [h_qₑ_div]
              rw [MulAdd.eq.AddMulS]
              simp [h_q'_div, h_r'_mod]
              simp [h_q_div, h_r_mod]
              rw [h_prod_drop]
              rw [DivDiv.eq.Div_Mul]
              conv_lhs => rw [Mul_Mul.eq.MulMul.comm]
              rw [Mul_Mul.eq.MulMul]
              simp [AddAdd.eq.Add_Add]
              rw [MulMul.comm]
              simp
              left
              simp [MulMul.comm]
              apply DivMod_Mul.eq.ModDiv
            ·
              simp [ProdTake.eq.MulProdTake.of.GtLength h_d_length]
            ·
              simp [h_prod_take]
              rw [EqDivMul.of.Ne_0 (by grind)]
              convert h_qₐ
              rwa [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength.simp]
          ·
            rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength.simp h_d_length h_i]
            rw [ProdEraseIdx.eq.MulProdS]
          ·
            simp [ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength]
        ·
          simp [ProdTake.eq.MulProdTake.of.GtLength h_d_lt_length]
        ·
          simp [ProdTake.eq.MulProdTake.of.GtLength h_d_lt_length]
          rwa [EqDivMul.of.Ne_0 (by grind)]
        ·
          rwa [GetSet.eq.Get.of.Gt.GtLength h_d_length h_d]
      ·
        simp
        rw [h_length_slice]
        rw [EraseIdxSet.eq.SetEraseIdx.of.Gt h_d]
        rw [h_prod_set]


-- created on 2025-11-29
