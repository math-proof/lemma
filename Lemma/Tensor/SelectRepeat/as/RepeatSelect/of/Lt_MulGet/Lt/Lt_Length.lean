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
import Lemma.List.ProdDrop.dvd.ProdDropEraseIdx.of.Gt
import Lemma.List.ProdDrop.eq.MulProdSDrop.of.Le
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.Lt_Length
import Lemma.List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Gt
import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.Lt_Length
import Lemma.List.ProdSet__Mul_Get.eq.Mul_Prod.of.Lt_Length
import Lemma.List.ProdTake.eq.MulProdTake.of.Lt_Length
import Lemma.List.ProdTakeSet.eq.Mul_ProdTake.of.Lt.Lt_Length
import Lemma.List.TakeEraseIdx.eq.Take.of.Ge
import Lemma.List.TakeSet.eq.SetTake.of.Lt
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.Dvd_Mul.of.Dvd
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Lt.of.Lt.Lt
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.ModAdd.eq.Mod.of.Dvd
import Lemma.Nat.DivMod_Mul.eq.ModDiv
import Lemma.Nat.Mod_Mul.eq.AddMul_Mod.of.Lt
import Lemma.Nat.Mod_Mul.eq.AddMul_Mod.of.Ne_0
import Lemma.Nat.Mul
import Lemma.Nat.MulAdd.eq.AddMulS
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
open Nat List Bool Tensor Vector


@[main]
private lemma main
-- given
  (h_d : d < s.length)
  (h_k : k < d)
  (h_i : i < s[d])
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.repeat n ⟨k, by grind⟩).select ⟨d, by grind⟩ ⟨i, by grind⟩ ≃ (X.select ⟨d, h_d⟩ ⟨i, h_i⟩).repeat n ⟨k, by grind⟩ := by
-- proof
  have h_get_eraseIdx := GetEraseIdx.eq.Get.of.Lt.Lt_Length h_d h_k
  apply SEq.of.SEqDataS.Eq
  ·
    simp [h_get_eraseIdx]
    grind
  ·
    rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0]
    conv_rhs => rw [DataRepeat.eq.Cast_FlattenMapSplitAtData]
    have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (s := s.set k (n * s[k])) (d := d) (i := i) (by grind) (by grind)
    simp at h_length_slice
    have h_prod_set := ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.Lt_Length (s := s.eraseIdx d) (i := k) (by grind) n
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
            have h_prod_take := ProdTake.eq.MulProdTake.of.Lt_Length h_d
            have h_lt : (↑q * s[d] + i) * ((s.set k (n * s[k])).drop (d + 1)).prod + ↑r < (s.take k).prod * (n * (s.drop k).prod) := by
              simp [DropSet.eq.Drop.of.Lt (show k < d + 1 by omega)] at ⊢ h_r
              rw [Mul_Mul.eq.MulMul]
              rw [MulMul.comm]
              simp
              rw [Mul.comm (b := n)]
              simp only [Prod.eq.MulProdS s (d + 1)]
              rw [Mul_Mul.eq.MulMul]
              apply AddMul.lt.Mul.of.Lt.Lt _ h_r
              rw [h_prod_take]
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
            let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
            repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
            rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin _ _ h_i]
            ·
              simp [GetRepeat.eq.Get_Mod.fin]
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              apply congrArg
              simp
              rw [ModAdd.eq.Mod.of.Dvd.left (Dvd_Mul.of.Dvd (ProdDrop.dvd.ProdDropEraseIdx.of.Gt h_k s) q')] at h_rₑ_mod
              simp [ProdDropEraseIdx.eq.ProdAppendDropTake.of.Gt h_k] at h_qₑ_div h_rₑ_mod h_q'_div h_r'_mod h_t
              rw [Mul_Mul.eq.MulMul] at h_qₑ_div
              rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₑ_div
              simp [h_rₑ_mod]
              simp [DropSet.eq.Drop.of.Lt (show k < d + 1 by omega)] at h_qₐ_div h_rₐ_mod h_q_div h_r_mod h_r
              rw [MulAdd.eq.AddMulS, MulMul.eq.Mul_Mul] at h_qₐ_div h_rₐ_mod ⊢
              rw [Mul_ProdDrop_Add_1.eq.ProdDrop.of.Lt_Length] at h_qₐ_div h_rₐ_mod ⊢
              have h_prod_drop := ProdDrop.eq.MulProdSDrop.of.Le (i := k) (j := d) (by omega) s
              simp [h_prod_drop] at h_qₐ_div
              simp [Mul_Mul.eq.MulMul] at h_qₐ_div
              simp [Div_Mul.eq.DivDiv.comm] at h_qₐ_div
              rw [AddAdd.eq.Add_Add] at h_qₐ_div
              rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₐ_div
              rw [Div.eq.Zero.of.Lt (n := (s.drop d).prod)] at h_qₐ_div
              ·
                simp [DivDiv.eq.Div_Mul.comm] at h_qₐ_div
                simp [h_qₐ_div, h_rₐ_mod]
                simp [h_qₑ_div]
                rw [MulAdd.eq.AddMulS]
                simp [h_r'_mod]
                simp [Mul_Mul.eq.MulMul]
                simp [h_q'_div]
                simp [h_q_div, h_r_mod]
                rw [TakeEraseIdx.eq.Take.of.Ge (by omega)] at h_t
                simp [Mul_Mul.eq.MulMul] at h_t
                rw [h_prod_drop]
                rw [ProdTakeSet.eq.Mul_ProdTake.of.Lt.Lt_Length (by omega) h_k] at h_q
                simp [Div_Mul.eq.DivDiv.comm]
                simp [AddAdd.eq.Add_Add]
                simp [Mul_Mul.eq.MulMul]
                rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.Lt_Length h_d]
                rw [Mul_Mul.eq.MulMul]
                rw [Add_Add.eq.AddAdd]
                rw [AddMulS.eq.MulAdd]
                rw [Mul_Mul.eq.MulMul]
                rw [Mod_Mul.eq.AddMul_Mod.of.Ne_0 (by grind)]
                rw [Mod_Mul.eq.AddMul_Mod.of.Lt h_i]
                rw [MulAdd.eq.AddMulS]
                simp [Add_Add.eq.AddAdd]
                simp [Mul_Mul.eq.MulMul]
                repeat left
                simp [Mul.comm (b := (s.drop (d + 1)).prod)]
                rw [DivMod_Mul.eq.ModDiv]
              ·
                rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.Lt_Length h_d]
                apply AddMul.lt.Mul.of.Lt.Lt h_i h_r
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
-- updated on 2025-11-22
