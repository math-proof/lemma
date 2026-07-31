import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.ProdTakeSet.eq.MulProdSetTake.of.Lt.GtLength
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
        rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        simp [GetSet.eq.Get.of.Lt.GtLength h_d h_k]
        rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
        simp [DataResize.eq.Cast_FlattenMapSplitAtData]
        have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength (s := s) (d := d) (i := i) (by grind) (by grind)
        rw [List.ProdTakeMapCast.eq.ProdTake] at h_length_slice
        rw [GetCast.eq.Get.of.Eq.fin (by simp [ProdSet.eq.MulProd_Mul_Prod.of.GtLength (Lt.of.Lt.Lt h_k h_d)])]
        have h_lt : (↑q * s[↑d] + ↑i) * ((s.set k n).drop (↑d + 1)).prod + ↑r < (s.take k).prod * (n * (s.drop (k + 1)).prod) := by
          rw [MulProd_Mul_Prod.eq.ProdSet.of.GtLength (by grind) n]
          apply AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop _ h_r
          apply Nat.lt_of_lt_of_eq _ (MulProdSetTake.eq.ProdTakeSet.of.Lt.GtLength h_d h_k n)
          apply AddMul.lt.Mul.of.Lt.Lt _ h_i
          rwa [TakeSet.eq.SetTake.of.Lt h_k] at h_q
        let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
        have h_qₑ := qₑ.isLt
        let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
        simp
        erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₑrₑ]
        simp [GetResize.eq.Ite_Get_Mod.fin]
        split_ifs with h₁ h₂ h₃
        ·
          simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
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
          generalize h_s_d : s[d] = s_d at *
          have h_s_d2 : s[↑d] = s_d := (Eq.refl (s[↑d])).trans h_s_d
          simp only [h_s_d2] at *
          have h_prod_drop := ProdDrop.eq.MulProdSDrop.of.Le (i := k) (j := d) (by omega) s
          have h_drop_set : ((s.set k n).drop (↑d + 1)).prod = (s.drop (↑d + 1)).prod := by rw [DropSet.eq.Drop.of.Lt (show k < ↑d + 1 by omega)]
          set A := (s.drop (↑d + 1)).prod with h_A
          set C := ((s.take ↑d).drop (k + 1)).prod with h_C
          have h_B' : ((s.eraseIdx ↑d).drop (k + 1)).prod = C * A := by
            rw [ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show ↑d ≥ k + 1 by omega)]
          have h_M' : ((s.eraseIdx ↑d).drop k).prod = s[k] * C * A := by
            rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength (show (s.eraseIdx ↑d).length > k by grind)]
            simp [GetEraseIdx.eq.Get.of.Gt.GtLength h_d h_k]
            rw [h_B']
            ring_nf
          have h_B : (s.drop (k + 1)).prod = s_d * C * A := by
            rw [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ d by omega)]
            rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength h_d]
            ring_nf
            sorry
          have h_M : (s.drop k).prod = s[k] * s_d * C * A := by
            rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength (show s.length > k by omega)]
            rw [h_B]
            ring_nf
          have h_A_pos := Nat.zero_lt_of_lt h_r
          have h_r_A : ↑r < A := by
            rw [← h_drop_set]
            grind
          have h_i_A : ↑i * A + ↑r < s_d * A := by
            nlinarith [h_i, h_r_A]
          have h_qr_A : ↑t = ↑q * A + ↑r := by
            rw [h_qr]
            simp [h_drop_set]
          have h_q'_eq : ↑q' = ↑q / (n * C) := by
            rw [h_q'_div]
            rw [h_qr_A]
            rw [h_B']
            rw [show n * (C * A) = A * (n * C) by ring_nf]
            rw [show (↑q * A + ↑r) / (A * (n * C)) = (↑q * A + ↑r) / A / (n * C) by
              rw [← DivDiv.eq.Div_Mul]]
            rw [show (↑q * A + ↑r) / A = ↑q by sorry]
          have h_r'_eq : ↑r' = (↑q % (n * C)) * A + ↑r := by
            rw [h_r'_mod]
            rw [h_qr_A]
            rw [h_B']
            rw [show n * (C * A) = n * C * A by ring_nf]
            rw [Mod_Mul.eq.AddMul_Mod.of.Lt h_r_A]
          have h_qₑ_eq : ↑qₑ = ↑q / (n * C) := by
            rw [h_qₑ_div]
            simp [h_drop_set]
            rw [h_B]
            rw [show n * (s_d * C * A) = (s_d * A) * (n * C) by ring_nf]
            rw [show ((↑q * s_d + ↑i) * A + ↑r) / ((s_d * A) * (n * C)) = ((↑q * s_d + ↑i) * A + ↑r) / (s_d * A) / (n * C) by
              rw [← DivDiv.eq.Div_Mul]]
            rw [show ((↑q * s_d + ↑i) * A + ↑r) / (s_d * A) = ↑q by sorry]
          have h_rₑ_eq : ↑rₑ = (↑q % (n * C) * s_d + ↑i) * A + ↑r := by
            rw [h_rₑ_mod]
            simp [h_drop_set]
            rw [h_B]
            rw [show n * (s_d * C * A) = (n * C) * (s_d * A) by ring_nf]
            rw [show (↑q * s_d + ↑i) * A + ↑r = ↑q * (s_d * A) + (↑i * A + ↑r) by ring_nf]
            rw [Mod_Mul.eq.AddMul_Mod.of.Lt h_i_A]
            ring_nf
          have h_r'_mod_M' : ↑r' % (s[k] * C * A) = (↑q % (n * C) % (s[k] * C)) * A + ↑r := by
            rw [h_r'_eq]
            rw [show s[k] * C * A = (s[k] * C) * A by ring_nf]
            rw [Mod_Mul.eq.AddMul_Mod.of.Lt h_r_A]
          have h_qₐ_eq : ↑qₐ = ↑q' * s[k] * C + (↑q % (n * C) % (s[k] * C)) := by
            rw [h_qₐ_div]
            simp [h_M']
            rw [show ↑q' * (s[k] * C * A) + (↑r' % (s[k] * C * A)) = (↑q' * s[k] * C + (↑q % (n * C) % (s[k] * C))) * A + ↑r by
              rw [h_r'_mod_M']
              ring_nf]
            rw [DivAddMul.eq.Add_Div.of.Gt_0 h_A_pos]
            rw [Div.eq.Zero.of.Lt h_r_A]
            ring_nf
          have h_rₐ_eq : ↑rₐ = r.val := by
            sorry
          rw [h_qₐ_eq, h_q'_eq, h_M, h_B]
          ring_nf
          sorry
        ·
          sorry
        ·
          sorry
        ·
          rfl
      ·
        simp [h_length_slice]
        rw [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k]
        rw [h_prod_set]


-- created on 2026-07-30
