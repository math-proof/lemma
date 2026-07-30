import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.List.DropSet.eq.SetDrop.of.Ge
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Gt
import Lemma.List.GetEraseIdx.eq.Get_Add_1.of.Le.LtAdd_1Length
import Lemma.List.GetSet.eq.Get.of.Gt.GtLength
import Lemma.List.LengthSet.eq.Length
import Lemma.List.LengthSlice.eq.ProdTake.of.GtGet.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
import Lemma.List.AddMul_ProdDrop.lt.Prod
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.List.ProdDrop.ne.Zero.of.NeProd_0
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.ProdDrop.eq.MulProdSDrop.of.Le
import Lemma.List.ProdTake.eq.Mul_ProdDropTake.of.Ge
import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.List.TakeSet.eq.Take.of.Ge
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.DivMod_Mul.eq.ModDiv
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.LtMod.of.Ne_0
import Lemma.Nat.ModMod.eq.Mod.of.Dvd
import Lemma.Nat.Mod_Mul.eq.AddMul_Mod.of.Ne_0
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Mul_Mul
import Lemma.Tensor.DataResize.as.FlattenMapSplitAtData
import Lemma.Tensor.DataSelect.as.FlattenGetSliceSplitAtData
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.GtGet.GtLength
import Lemma.Vector.GetResize.eq.Ite_Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open List Nat Bool Tensor Vector Fin
set_option maxHeartbeats 2000000


@[main, cast]
private lemma main
  [Zero α]
-- given
  (h_k : s.length > k)
  (h_d : k > d)
  (X : Tensor α s)
  (i : Fin s[d])
  (n : ℕ) :
-- imply
  (X.resize ⟨k, h_k⟩ n).select ⟨d, by grind⟩ ⟨i, by grind⟩ ≃ (X.select ⟨d, by grind⟩ i).resize ⟨k - 1, by grind⟩ n := by
-- proof
  have h_i := i.isLt
  have h_get_eraseIdx : (s.eraseIdx d)[k - 1]'(by grind) = s[k] := by
    rw [GetEraseIdx.eq.Get_Add_1.of.Le.LtAdd_1Length (by omega) (by omega)]
    simp [EqAddSub.of.Ge (show k ≥ 1 by omega)]
  apply SEq.of.SEqDataS.Eq
  ·
    simp [h_get_eraseIdx]
    rw [EraseIdxSet.eq.SetEraseIdx.of.Gt h_d]
  ·
    rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData]
    conv_rhs => rw [DataResize.eq.Cast_FlattenMapSplitAtData]
    have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength (s := s.set k n) (d := d) (i := i) (by grind) (by grind)
    simp at h_length_slice
    have h_prod_set := ProdSet.eq.MulProd_Mul_Prod.of.GtLength (s := s.eraseIdx d) (i := k - 1) (by grind) n
    have h_d_length : d < s.length := by omega
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp [← h_length_slice]
    ·
      simp [h_prod_set]
    ·
      simp [List.Vector.length]
      apply SEq.of.All_EqGetS.Eq.fin
      ·
        intro t
        have h_t := t.isLt
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        have h_q := q.isLt
        have h_r := r.isLt
        have h_d_lt_length := LengthSet.eq.Length s k n ▸ h_k
        have h_d_lt_length := h_d.trans h_d_lt_length
        have := LengthSlice.eq.ProdTake.of.GtGet.GtLength (i := i) (d := d) (s := s.set k n) (by grind) (by grind)
        simp at this
        simp [this] at h_q
        let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        simp [h_length_slice] at h_t
        rw [EraseIdxSet.eq.SetEraseIdx.of.Gt h_d] at h_t
        rw [h_prod_set] at h_t
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
        simp
        rw [GetGetSlice.eq.Get.of.GtGet.GtLength (by grind) (by grind)]
        simp [GetResize.eq.Ite_Get_Mod.fin]
        repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        simp [GetSet.eq.Get.of.Gt.GtLength h_d_length h_d]
        simp [DataSelect.eq.Cast_FlattenGetSliceSplitAtData]
        simp [DataResize.eq.Cast_FlattenMapSplitAtData]
        have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength (s := s) (d := d) (i := i) (by grind) (by grind)
        repeat rw [GetCast.eq.Get.of.Eq.fin]
        ·
          have h_prod_take := ProdTake.eq.MulProdTake.of.GtLength h_d_length
          simp [List.Vector.length]
          have h_lt : (↑q * s[d] + i) * ((s.set k n).drop (d + 1)).prod + ↑r < (s.take k).prod * (n * (s.drop k).prod) := by
            have h_prod_take' :
                ((s.set k n).take (d + 1)).prod = (s.take (d + 1)).prod := by
              simp [TakeSet.eq.Take.of.Ge (show k ≥ d + 1 by omega) n, ProdTake.eq.MulProdTake.of.GtLength h_d_length]
            have h_row₀ : (↑q * s[d] + ↑i) < (s.take (d + 1)).prod := by
              rw [ProdTake.eq.MulProdTake.of.GtLength h_d_length]
              apply AddMul.lt.Mul.of.Lt.Lt _ h_i
              simpa [TakeSet.eq.Take.of.Ge (show k ≥ d by omega) n] using h_q
            have h_row : (↑q * s[d] + ↑i) < ((s.set k n).take (d + 1)).prod :=
              Nat.lt_of_lt_of_eq h_row₀ h_prod_take'.symm
            have h_lt₀ :=
              AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop
                (s := s.set k n) (d := d + 1) h_row h_r
            have h_le : (s.set k n).prod ≤ (s.take k).prod * (n * (s.drop k).prod) := by
              rw [ProdSet.eq.MulProd_Mul_Prod.of.GtLength (by omega) n]
              rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength (show s.length > k by omega)]
              simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
              exact Nat.le_refl
            exact Nat.lt_of_lt_of_le h_lt₀ h_le
          let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
          let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
          have h_lt : ↑q' * ((s.eraseIdx d).drop (k - 1)).prod + ↑r' % ((s.eraseIdx d).drop (k - 1)).prod < (⟨↑i, ↑(s.take (d + 1)).prod, ↑s[d]⟩ : Slice).length (s.take (d + 1)).prod * (s.drop (d + 1)).prod := by
            simp [h_length_slice]
            rw [Prod.eq.MulProdS (s.eraseIdx d) (k - 1)]
            apply AddMul.lt.Mul.of.Lt.Lt q'.isLt
            apply LtMod.of.Gt_0
            grind
          let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
          have h_qₑ := qₑ.isLt
          let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
          repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
          rw [GetGetSlice.eq.Get.of.GtGet.GtLength h_d_length h_i]
          simp [GetResize.eq.Ite_Get_Mod.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          split_ifs
          ·
            apply congrArg
            simp
            simp [DropEraseIdx.eq.Drop.of.Le (show d ≤ k - 1 by omega)] at h_qₑ_div h_rₑ_mod h_q'_div h_r'_mod
            rw [EqAddSub.of.Ge (show k ≥ 1 by omega)] at h_qₑ_div h_rₑ_mod h_q'_div h_r'_mod
            simp [DropSet.eq.SetDrop.of.Ge (show k ≥ d + 1 by omega)] at h_qₐ_div h_rₐ_mod h_q_div h_r_mod
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
            simp
            grind
        ·
          simp [h_length_slice]
        ·
          simp [ProdSet.eq.MulProd_Mul_Prod.of.GtLength h_k]
      ·
        simp
        rw [h_length_slice]
        rw [EraseIdxSet.eq.SetEraseIdx.of.Gt h_d]
        rw [h_prod_set]


-- created on 2026-07-30
