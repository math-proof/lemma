import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Gt
import Lemma.List.GetEraseIdx.eq.Get_Add_1.of.Le.LtAdd_1Length
import Lemma.List.GetSet.eq.Get.of.Gt.Lt_Length
import Lemma.List.LengthSet.eq.Length
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.ProdDrop.eq.MulProdSDrop.of.Le
import Lemma.List.ProdDropSet__Mul_Get.eq.Mul_ProdDrop.of.Ge.Lt_Length
import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.List.ProdTake.eq.MulProdTake.of.Lt_Length
import Lemma.List.TakeSet.eq.Take.of.Ge
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.DivMod_Mul.eq.ModDiv
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.LtMod.of.Ne_0
import Lemma.Nat.Mod_Mul.eq.AddMul_Mod.of.Ne_0
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Mul_Mul
import Lemma.Tensor.DataRepeat.eq.Cast_FlattenMapSplitAtData
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open List Nat Bool Tensor Vector


@[main]
private lemma main
-- given
  (h_k : s.length > k)
  (h_d : k > d)
  (h_i : i < s[d])
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.repeat n ⟨k, h_k⟩).select ⟨d, by grind⟩ ⟨i, by grind⟩ ≃ (X.select ⟨d, by grind⟩ ⟨i, h_i⟩).repeat n ⟨k - 1, by grind⟩ := by
-- proof
  have h_get_eraseIdx : (s.eraseIdx d)[k - 1]'(by grind) = s[k] := by
    rw [GetEraseIdx.eq.Get_Add_1.of.Le.LtAdd_1Length (by omega) (by omega)]
    simp [EqAddSub.of.Ge (show k ≥ 1 by omega)]
  apply SEq.of.SEqDataS.Eq
  ·
    simp [h_get_eraseIdx]
    rw [EraseIdxSet.eq.SetEraseIdx.of.Gt h_d]
  ·
    rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0]
    conv_rhs => rw [DataRepeat.eq.Cast_FlattenMapSplitAtData]
    have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (s := s.set k (n * s[k])) (d := d) (i := i) (by grind) (by grind)
    simp at h_length_slice
    have h_prod_set := ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength (s := s.eraseIdx d) (i := k - 1) (by grind) n
    have h_d_length : d < s.length := by omega
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp [← h_length_slice]
    ·
      simp [h_prod_set]
    ·
      rw [h_get_eraseIdx] at h_prod_set
      simp [List.Vector.length]
      apply SEq.of.All_EqGetS.Eq.fin
      ·
        intro t
        have h_t := t.isLt
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        have h_q := q.isLt
        have h_r := r.isLt
        have h_d_lt_length := LengthSet.eq.Length s k (n * s[k]) ▸ h_k
        have h_d_lt_length := h_d.trans h_d_lt_length
        have := LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (i := i) (d := d) (s := s.set k (n * s[k])) (by grind) (by grind)
        simp at this
        simp [this] at h_q
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
          simp [GetSet.eq.Get.of.Gt.Lt_Length h_d_length h_d]
          simp [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0]
          simp [DataRepeat.eq.Cast_FlattenMapSplitAtData]
          have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (s := s) (d := d) (i := i) (by grind) (by grind)
          repeat rw [GetCast.eq.Get.of.Eq.fin]
          ·
            have h_prod_take := ProdTake.eq.MulProdTake.of.Lt_Length h_d_length
            simp [List.Vector.length]
            have h_lt : (↑q * s[d] + i) * ((s.set k (n * s[k])).drop (d + 1)).prod + ↑r < (s.take k).prod * (n * (s.drop k).prod) := by
              simp [ProdDropSet__Mul_Get.eq.Mul_ProdDrop.of.Ge.Lt_Length h_k (show k ≥ d + 1 by omega)] at ⊢ h_r
              conv_rhs => rw [Mul_Mul.eq.MulMul]
              conv_rhs => rw [MulMul.comm]
              simp
              rw [Prod.eq.MulProdS s (d + 1)]
              rw [MulMul.comm, MulMul.eq.Mul_Mul]
              apply AddMul.lt.Mul.of.Lt.Lt _ h_r
              rw [h_prod_take]
              apply AddMul.lt.Mul.of.Lt.Lt _ h_i
              rwa [TakeSet.eq.Take.of.Ge (show k ≥ d by omega)] at h_q
            let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
            let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
            have h_lt : ↑q' * ((s.eraseIdx d).drop (k - 1)).prod + ↑r' % ((s.eraseIdx d).drop (k - 1)).prod < (⟨↑i, ↑(s.take (d + 1)).prod, ↑s[d]⟩ : Slice).length (s.take (d + 1)).prod * (s.drop (d + 1)).prod := by
              simp [h_length_slice]
              rw [Prod.eq.MulProdS (s.eraseIdx d) (k - 1)]
              apply AddMul.lt.Mul.of.Lt.Lt q'.isLt
              apply LtMod.of.Gt_0
              grind
            let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
            have h_qₑ := qₑ.isLt
            let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
            repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
            rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin _ _ h_i]
            ·
              simp [GetRepeat.eq.Get_Mod.fin]
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              apply congrArg
              simp
              simp [DropEraseIdx.eq.Drop.of.Le (show d ≤ k - 1 by omega)] at h_qₑ_div h_rₑ_mod h_q'_div h_r'_mod
              rw [EqAddSub.of.Ge (show k ≥ 1 by omega)] at h_qₑ_div h_rₑ_mod h_q'_div h_r'_mod
              simp [ProdDropSet__Mul_Get.eq.Mul_ProdDrop.of.Ge.Lt_Length h_k (show k ≥ d + 1 by omega)] at h_qₐ_div h_rₐ_mod h_q_div h_r_mod
              simp [ProdDrop.eq.MulProdSDrop.of.Le (show d + 1 ≤ k by omega) s] at *
              rw [Mod_Mul.eq.AddMul_Mod.of.Ne_0 (by grind)] at *
              rw [Mul_Mul.comm (a := n)] at h_qₐ_div h_rₐ_mod
              rw [Mul_Mul.eq.MulMul] at h_qₐ_div h_rₐ_mod
              simp [Div_Mul.eq.DivDiv.comm] at h_qₑ_div
              rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₐ_div h_qₑ_div
              simp at h_rₐ_mod
              rw [Mul_Mul.eq.MulMul] at h_r_mod
              simp [h_rₑ_mod, h_rₐ_mod, h_r'_mod, h_r_mod]
              simp [Add_Add.eq.AddAdd]
              rw [Mul_Mul.eq.MulMul]
              simp [AddMulS.eq.MulAdd]
              left
              simp [h_qₐ_div]
              simp [MulAdd.eq.AddMulS]
              simp [AddAdd.comm]
              rw [Div.eq.Zero.of.Lt (n := (s.drop k).prod)] at h_qₑ_div
              ·
                simp at h_qₑ_div
                simp [h_qₑ_div, h_q'_div, h_q_div]
                rw [DivDiv.eq.Div_Mul]
                rw [MulMul.comm (a := n)]
                simp [Mul_Mul.eq.MulMul]
                rw [MulMul.comm] at h_r_mod
                simp [h_r_mod]
                rw [DivMod_Mul.eq.ModDiv]
              ·
                apply LtMod.of.Ne_0
                grind
            ·
              simp [h_prod_take]
            ·
              have h_length_slice := LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (s := s) (d := d) (i := i) (by grind) (by grind)
              simp at h_length_slice
              simp [h_length_slice] at h_qₑ
              simp [h_prod_take]
              rwa [EqDivMul.of.Ne_0 (by grind)]
          ·
            simp [h_length_slice]
          ·
            simp [ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength h_k]
        ·
          simp [ProdTake.eq.MulProdTake.of.Lt_Length h_d_lt_length]
        ·
          simp [ProdTake.eq.MulProdTake.of.Lt_Length h_d_lt_length]
          rwa [EqDivMul.of.Ne_0 (by grind)]
        ·
          rwa [GetSet.eq.Get.of.Gt.Lt_Length h_d_length h_d]
      ·
        simp
        rw [h_length_slice]
        rw [EraseIdxSet.eq.SetEraseIdx.of.Gt h_d]
        rw [h_prod_set]


-- created on 2025-11-22
