import Lemma.List.MulLengthSlice_Mul.eq.ProdEraseIdx.of.GtGet.GtLength
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.DropSet.eq.Drop.of.Lt
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Lt
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.List.GetSet.eq.Get.of.Lt.GtLength
import Lemma.List.LengthSet.eq.Length
import Lemma.List.LengthSlice.eq.ProdTake.of.GtGet.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.ProdDrop.dvd.ProdDropEraseIdx.of.Ge
import Lemma.List.ProdDrop.eq.MulProdSDrop.of.Le
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge
import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.AddMul_ProdDrop.lt.Prod
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.List.SetAppend.eq.Append_Set.of.GtLength
import Lemma.List.Take.eq.AppendTake.of.GtLength
import Lemma.List.TakeSet.eq.SetTake.of.Lt
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.Dvd_Mul.of.Dvd
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
import Lemma.Tensor.DataResize.as.FlattenMapSplitAtData
import Lemma.Tensor.DataSelect.as.FlattenGetSliceSplitAtData
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.GtGet.GtLength
import Lemma.Vector.GetResize.eq.Ite_Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat List Bool Tensor Vector Fin
set_option maxHeartbeats 8000000


@[main, cast]
private lemma main
  [Zero α]
  {d : Fin s.length}
  {k : ℕ}
-- given
  (h_k : k < d)
  (X : Tensor α s)
  (i : Fin s[d])
  (n : ℕ) :
-- imply
  (X.resize ⟨k, h_k.trans d.isLt⟩ n).select ⟨d, by grind⟩ ⟨i, by grind⟩ ≃ (X.select d i).resize ⟨k, by grind⟩ n := by
-- proof
  have h_i : i < s[d.val] := i.isLt
  have h_d := d.isLt
  apply SEq.of.SEqDataS.Eq
  ·
    simp
    grind
  ·
    rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
    conv_rhs => rw [DataResize.eq.Cast_FlattenMapSplitAtData]
    have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength (s := s.set k n) (d := d) (i := i) (by grind) (by grind)
    rw [List.ProdTakeMapCast.eq.ProdTake] at h_length_slice
    simp at h_length_slice
    have h_prod_set := ProdSet.eq.MulProd_Mul_Prod.of.GtLength (s := s.eraseIdx d) (i := k) (by grind) n
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp [← h_length_slice]
    ·
      simp [h_prod_set]
    ·
      simp
      apply SEq.of.All_EqGetS.Eq.fin
      ·
        intro t
        have h_t := t.isLt
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        have h_q := q.isLt
        have h_r := r.isLt
        have h_s := LengthSet.eq.Length s k n
        have h_d_lt_length := h_d
        simp only [← h_s] at h_d_lt_length
        have := LengthSlice.eq.ProdTake.of.GtGet.GtLength (i := i) h_d_lt_length (show ↑i < (s.set k n)[d.val] by grind)
        rw [List.ProdTakeMapCast.eq.ProdTake] at this
        simp only [this] at h_q
        let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        simp [h_length_slice] at h_t
        rw [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k] at h_t
        rw [h_prod_set] at h_t
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
        simp
        rw [GetGetSlice.eq.Get.of.GtGet.GtLength (by grind) (by grind)]
        simp [GetResize.eq.Ite_Get_Mod.fin]
        repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        simp [GetSet.eq.Get.of.Lt.GtLength h_d h_k]
        rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
        simp [DataResize.eq.Cast_FlattenMapSplitAtData]
        have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength (s := s) (d := d) (i := i) (by grind) (by grind)
        rw [List.ProdTakeMapCast.eq.ProdTake] at h_length_slice
        repeat rw [GetCast.eq.Get.of.Eq.fin]
        ·
          have h_lt : (↑q * s[↑d] + ↑i) * ((s.set k n).drop (↑d + 1)).prod + ↑r < (s.take k).prod * (n * (s.drop (k + 1)).prod) := by
            have h_row₀ : (↑q * s[↑d] + ↑i) < ((s.take ↑d).set k n).prod * s[↑d] := by
              apply AddMul.lt.Mul.of.Lt.Lt _ h_i
              rw [TakeSet.eq.SetTake.of.Lt h_k] at h_q
              have hpt := ProdSet.eq.MulProd_Mul_Prod.of.GtLength (s := s.take d) (i := k) (by simp; grind) n
              have htake : (s.take d).take k = s.take k := by grind
              simp [htake] at hpt
              exact h_q
            have h_take_prod : ((s.set k n).take (↑d + 1)).prod = ((s.take ↑d).set k n).prod * s[↑d] := by
              have h_append : (s.set k n).take (↑d + 1) = (s.take ↑d).set k n ++ [s[↑d]] := by
                rw [TakeSet.eq.SetTake.of.Lt (show k < ↑d + 1 by omega)]
                rw [Take.eq.AppendTake.of.GtLength h_d]
                rw [SetAppend.eq.Append_Set.of.GtLength (show k < (s.take ↑d).length by simp; omega)]
                grind
              rw [h_append, ProdAppend.eq.MulProdS]
              simp
            have h_row : (↑q * s[↑d] + ↑i) < ((s.set k n).take (↑d + 1)).prod := Nat.lt_of_lt_of_eq h_row₀ h_take_prod.symm
            have h_lt₀ := AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop (s := s.set k n) (d := ↑d + 1) h_row h_r
            rwa [← ProdSet.eq.MulProd_Mul_Prod.of.GtLength (by grind) n]
          let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
          have h_qₑ := qₑ.isLt
          let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
          simp
          erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₑrₑ]
          simp [GetResize.eq.Ite_Get_Mod.fin]
          split_ifs with h₁ h₂
          ·
            erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            simp
            erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            simp
            rw [GetCast.eq.Get.of.Eq.fin (by grind)]
            simp
            have h_lt : ↑q' * ((s.eraseIdx d).drop k).prod + ↑r' % ((s.eraseIdx d).drop k).prod < (⟨↑i, ↑(s.take (d + 1)).prod, s[d.val]⟩ : Slice).length (s.take (d + 1)).prod * (s.drop (d + 1)).prod := by
              rw [h_length_slice]
              rw [Prod.eq.MulProdS (s.eraseIdx d) k]
              apply AddMul.lt.Mul.of.Lt.Lt q'.isLt
              apply LtMod.of.Gt_0
              grind
            let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
            have h_qₐ := qₐ.isLt
            let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
            erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
            erw [Vector.GetGetSlice.eq.Get.of.GtGet.GtLength (by grind) (by grind)]
            erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            apply congrArg
            simp
            have h_k' := Le.of.Lt h_k
            rw [ModAdd.eq.Mod.of.Dvd.left (Dvd_Mul.of.Dvd (ProdDrop.dvd.ProdDropEraseIdx.of.Ge h_k' s) q')] at h_rₐ_mod
            simp at h_qₑ_div h_rₑ_mod h_q'_div h_r'_mod h_t
            simp [h_rₑ_mod, h_qₑ_div, h_rₐ_mod]
            simp [DropSet.eq.Drop.of.Lt (show k < d + 1 by omega)] at h_qₐ_div h_rₐ_mod h_q_div h_r_mod h_r
            simp [MulAdd.eq.AddMulS, MulMul.eq.Mul_Mul] at h_qₐ_div h_rₐ_mod ⊢
            have h_prod_drop := ProdDrop.eq.MulProdSDrop.of.Le (i := k) (j := d) (by omega) s
            sorry
          ·
            erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            exfalso
            sorry
          ·
            erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            simp
            sorry
          ·
            rfl
        ·
          simp [ProdSet.eq.MulProd_Mul_Prod.of.GtLength (Lt.of.Lt.Lt h_k h_d)]
      ·
        simp [h_length_slice]
        rw [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k]
        rw [h_prod_set]


-- created on 2026-07-30
