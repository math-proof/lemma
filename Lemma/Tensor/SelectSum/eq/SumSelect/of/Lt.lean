import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Finset.Sum.of.All_Eq.Eq
import Lemma.List.DropEraseIdx.eq.AppendDropTake.of.Ge
import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.List.DropEraseIdx.eq.Drop.of.Lt
import Lemma.List.EraseIdxEraseIdx.of.Gt.GtLength
import Lemma.List.EraseIdxTake.eq.Take
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.GtLength
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.ProdDrop.eq.MulProdSDrop.of.Le
import Lemma.List.ProdDropTake.eq.MulProdDropTake.of.Gt.GtLength
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.List.ProdEraseIdx.eq.MulProdS.of.Lt
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.List.ProdTake.eq.Mul_ProdDropTake.of.Ge
import Lemma.List.TakeEraseIdx.eq.EraseIdxTake.of.Le
import Lemma.List.TakeEraseIdx.eq.Take.of.Gt
import Lemma.List.TakeTake.eq.Take.of.Gt
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Ne_0
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.DivMod_Mul.eq.ModDiv
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Mod_Mul.eq.AddMul_Mod.of.Lt
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.ValCast.eq.Val.of.Eq
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.DataSum.eq.Sum_DataSelect
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSum.eq.Sum_Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.Sum.of.All_Eq.Eq
open Bool Finset List Nat Tensor Vector Fin
set_option maxHeartbeats 4000000


@[main, comm]
private lemma main
  [AddCommMonoid α]
  {d : Fin s.length}
  {k : ℕ}
-- given
  (h_k : k < d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.sum k).select ⟨d - 1, by grind⟩ ⟨i, by grind⟩ ≃ (X.select d i).sum k := by
-- proof
  have h_d := d.isLt
  have h_k_length := h_k.trans h_d
  have h_i : i < s[d.val] := i.isLt
  apply SEq.of.SEqDataS.Eq
  ·
    rwa [← EraseIdxEraseIdx.of.Gt.GtLength h_k_length]
  ·
    rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
    apply SEqCast.of.SEq.Eq
    ·
      simp
      rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
      grind
    ·
      rw [DataSum.eq.Sum_DataSelect (X.select d i) ⟨k, by grind⟩]
      apply SEq.of.All_EqGetS.Eq.fin
      ·
        intro t
        have h_t := t.isLt
        simp
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        have h_q' := q'.isLt
        simp at h_q'
        have h_i_lt : ↑i < (s.eraseIdx k)[↑d - 1]'(by grind) := by
          rw [GetEraseIdx.eq.Get.of.Lt.GtLength h_d h_k]
          grind
        rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (by grind) h_i_lt] at h_q'
        have h_r' := r'.isLt
        simp [DropEraseIdx.eq.Drop.of.Le (show k ≤ d - 1 + 1 by omega)] at h_r'
        simp [EqAddSub.of.Ge (show d.val ≥ 1 by omega)] at h_r' h_q'_div h_r'_mod
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
        rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin.fin _ _ h_i_lt]
        ·
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          rw [GetSum.eq.Sum_Get.fin]
          simp [GetEraseIdx.eq.Get.of.Lt.GtLength h_d h_k]
          simp [DropEraseIdx.eq.Drop.of.Le (show k ≤ d - 1 + 1 by omega)]
          simp [show d.val - 1 + 1 = d by omega]
          rw [DataSum.eq.Sum_DataSelect X ⟨k, h_k_length⟩]
          rw [GetSum.eq.Sum_Get.fin]
          have h_cast := (GetEraseIdx.eq.Get.of.Gt.GtLength h_d h_k).symm
          apply @Finset.Sum.of.All_Eq.Eq (h_n := h_cast)
          intro j
          have h_j := j.isLt
          rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
          rw [GetCast.eq.Get.of.Eq.fin]
          ·
            simp
            rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              simp
              simp at h_t
              rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (by grind) (by omega)] at h_t
              have h_lt : t < (⟨↑↑(cast (congrArg Fin h_cast) j), ↑((s.eraseIdx ↑d).take (k + 1)).prod, (s.eraseIdx ↑d)[k]'(by grind)⟩ : Slice).length ((s.eraseIdx ↑d).take (k + 1)).prod * ((s.eraseIdx ↑d).drop (k + 1)).prod := by
                simp
                rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
                rwa [EraseIdxEraseIdx.of.Gt.GtLength (by omega) (by omega)]
                grind
              let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
              have h_q := q.isLt
              have h_r := r.isLt
              simp at h_q
              rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (by grind) (by grind)] at h_q
              let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
              have h_lt : (↑q' * s[↑d] + ↑i) * (s.drop (↑d + 1)).prod + ↑r' < ((⟨↑↑j, ↑(s.take (k + 1)).prod, ↑s[k]⟩ : Slice).length (s.take (k + 1)).prod) * (s.drop (k + 1)).prod := by
                simp
                rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength _ h_j]
                rw [ProdEraseIdx.eq.MulProdS]
                rw [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ d + 1 by omega)]
                rw [Mul_Mul.eq.MulMul]
                apply AddMul.lt.Mul.of.Lt.Lt
                ·
                  rw [ProdDropTake.eq.MulProdDropTake.of.Gt.GtLength h_d h_k]
                  rw [Mul_Mul.eq.MulMul]
                  apply AddMul.lt.Mul.of.Lt.Lt _ i.isLt
                  rw [TakeEraseIdx.eq.EraseIdxTake.of.Le (show k ≤ d - 1 by omega)] at h_q'
                  simp [EqAddSub.of.Ge (show d.val ≥ 1 by omega)] at h_q'
                  rw [ProdEraseIdx.eq.MulProdS] at h_q'
                  rw [TakeTake.eq.Take.of.Gt h_k] at h_q'
                  exact h_q'
                ·
                  exact h_r'
              let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
              have h_qₑ := qₑ.isLt
              simp at h_qₑ
              rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (by grind) (by grind)] at h_qₑ
              let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := qₑ) (j := rₑ)]
              ·
                rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin.fin _ _ h_j]
                ·
                  rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
                  rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin.fin]
                  ·
                    repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                    rw [GetCast.eq.Get.of.Eq.fin]
                    ·
                      simp [h_cast.symm]
                      simp [ValCast.eq.Val.of.Eq h_cast]
                      simp [DropEraseIdx.eq.AppendDropTake.of.Ge h_k]
                      let h_lt : (↑q * s[k] + ↑j) * (((s.take ↑d).drop (k + 1)).prod * (s.drop (↑d + 1)).prod) + ↑r < (⟨↑↑i, ↑(s.take (↑d + 1)).prod, ↑s[d]⟩ : Slice).length (s.take (↑d + 1)).prod * (s.drop (↑d + 1)).prod := by
                        simp
                        rw [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength d.isLt i.isLt]
                        rw [ProdEraseIdx.eq.MulProdS.of.Lt (show d < d.val + 1 by omega)]
                        rw [EraseIdxTake.eq.Take]
                        rw [ProdTake.eq.Mul_ProdDropTake.of.Ge h_k]
                        rw [MulMul.eq.Mul_Mul]
                        apply AddMul.lt.Mul.of.Lt.Lt
                        ·
                          rw [ProdTake.eq.MulProdTake.of.GtLength h_k_length]
                          rw [TakeEraseIdx.eq.Take.of.Gt h_k] at h_q
                          apply AddMul.lt.Mul.of.Lt.Lt h_q h_j
                        ·
                          simp [DropEraseIdx.eq.AppendDropTake.of.Ge h_k] at h_r
                          exact h_r
                      let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
                      have h_qₐ := qₐ.isLt
                      simp at h_qₐ
                      have := LengthSlice.eq.ProdTake.of.Lt_Get.GtLength d.isLt i.isLt
                      simp at this
                      simp [this] at h_qₐ
                      let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                      rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
                      rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin.fin]
                      ·
                        rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                        apply congrArg
                        simp [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ d + 1 by omega) s] at ⊢ h_qₑ_div h_rₑ_mod
                        rw [ProdDropTake.eq.MulProdDropTake.of.Gt.GtLength h_d h_k] at ⊢ h_qₑ_div h_rₑ_mod
                        repeat rw [Div_Mul.eq.DivDiv.comm] at h_qₑ_div
                        rw [DivAddMul.eq.Add_Div.of.Ne_0 (by grind)] at h_qₑ_div
                        rw [AddAdd.eq.Add_Add] at h_qₑ_div
                        rw [DivAddMul.eq.Add_Div.of.Ne_0 (by grind)] at h_qₑ_div
                        repeat rw [Mod_Mul.eq.AddMul_Mod.of.Lt (by assumption)] at h_rₑ_mod
                        simp [h_rₑ_mod]
                        repeat rw [MulAdd.eq.AddMulS]
                        repeat rw [Add_Add.eq.AddAdd]
                        rw [AddAdd.comm]
                        conv_rhs => rw [AddAdd.comm]
                        simp
                        rw [Mul_Mul.eq.MulMul] at h_qₐ_div h_rₐ_mod
                        rw [DivAddMul.eq.Add_Div.of.Ne_0 (by grind)] at h_qₐ_div
                        simp at h_rₐ_mod
                        simp [h_rₐ_mod]
                        simp [DropEraseIdx.eq.AppendDropTake.of.Ge h_k] at h_q_div h_r_mod
                        rw [DropEraseIdx.eq.Drop.of.Lt h_k] at h_q'_div h_r'_mod
                        simp [h_r_mod, h_r'_mod]
                        rw [AddMulS.eq.MulAdd]
                        rw [Mul_Mul.eq.MulMul]
                        simp [AddMulS.eq.MulAdd]
                        left
                        rw [Mul_Mul.eq.MulMul]
                        simp [AddMulS.eq.MulAdd]
                        left
                        simp [h_qₐ_div]
                        repeat rw [MulAdd.eq.AddMulS]
                        rw [AddAdd.comm]
                        conv_rhs => rw [AddAdd.comm]
                        simp [h_q_div, h_r_mod]
                        simp [h_qₑ_div]
                        simp [h_q'_div, h_r'_mod]
                        simp [Div.eq.Zero.of.Lt h_i]
                        simp [DivDiv.eq.Div_Mul.comm]
                        rw [DivMod_Mul.eq.ModDiv.comm]
                      ·
                        simp [ProdTake.eq.MulProdTake.of.GtLength d.isLt]
                      ·
                        simp [ProdTake.eq.MulProdTake.of.GtLength d.isLt]
                        rwa [EqDivMul.of.Ne_0 (by grind)]
                      ·
                        exact i.isLt
                    ·
                      simp [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength d.isLt i.isLt]
                  ·
                    simp [ProdTake.eq.MulProdTake.of.GtLength (show (s.eraseIdx ↑d).length > k by grind)]
                  ·
                    simp [ProdTake.eq.MulProdTake.of.GtLength (show (s.eraseIdx ↑d).length > k by grind)]
                    rwa [EqDivMul.of.Ne_0 (by grind)]
                  ·
                    rw [ValCast.eq.Val.of.Eq h_cast]
                    omega
                ·
                  simp [ProdTake.eq.MulProdTake.of.GtLength h_k_length]
                ·
                  simp [ProdTake.eq.MulProdTake.of.GtLength h_k_length]
                  rwa [EqDivMul.of.Ne_0 (by grind)]
              ·
                exact h_qₑrₑ
            ·
              simp
              rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
              grind
          ·
            simp
            rwa [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
        ·
          simp [ProdTake.eq.MulProdTake.of.GtLength (show (s.eraseIdx k).length > ↑d - 1 by grind)]
        ·
          simp [ProdTake.eq.MulProdTake.of.GtLength (show (s.eraseIdx k).length > ↑d - 1 by grind)]
          rwa [EqDivMul.of.Ne_0 (by grind)]
      ·
        simp
        rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (by grind)]
        rwa [← EraseIdxEraseIdx.of.Gt.GtLength (by omega)]
        grind


-- created on 2025-11-28
-- updated on 2025-11-29
