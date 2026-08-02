import Lemma.Nat.GeMul.of.Gt_0
import Lemma.Nat.SubAdd.eq.AddSub.of.Ge
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Gt
import Lemma.List.GetSet.eq.Get.of.Gt.GtLength
import Lemma.List.LengthSlice.eq.ProdTake.of.GtGet.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.ProdDrop.eq.MulProdSDrop.of.Le
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.List.ProdDropSet.eq.MulProdDropTake.of.Ge.GtLength
import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.List.TakeSet.eq.Take.of.Ge
import Lemma.Nat.AddAdd
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.DivMod.eq.Zero
import Lemma.Nat.DivMod_Mul.eq.ModDiv
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.ModMod_Mul.eq.Mod
import Lemma.Nat.Mod_Mul.eq.AddMul_Mod.of.Ne_0
import Lemma.Nat.Mod_Mul.eq.Add_Mul_ModDiv
import Lemma.Nat.ModAdd_Mul.eq.Mod
import Lemma.Nat.Div.eq.Zero.of.Lt
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
open Bool Fin List Nat Tensor Vector
set_option maxHeartbeats 4000000


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
  apply SEq.of.SEqDataS.Eq
  ·
    simp
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
        let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        have h_q := q.isLt
        have h_r := r.isLt
        have := LengthSlice.eq.ProdTake.of.GtGet.GtLength (i := i) (d := d) (s := s.set k n) (by grind) (by grind)
        simp at this
        simp [this] at h_q
        simp [h_length_slice] at h_t
        rw [EraseIdxSet.eq.SetEraseIdx.of.Gt h_d] at h_t
        rw [h_prod_set] at h_t
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
        simp
        rw [GetGetSlice.eq.Get.of.GtGet.GtLength (by grind) (by grind)]
        repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        simp [GetSet.eq.Get.of.Gt.GtLength h_d_length h_d]
        simp [DataSelect.eq.Cast_FlattenGetSliceSplitAtData]
        simp [DataResize.eq.Cast_FlattenMapSplitAtData]
        have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength (s := s) (d := d) (i := i) (by grind) (by grind)
        rw [GetCast.eq.Get.of.Eq.fin (by simp [ProdSet.eq.MulProd_Mul_Prod.of.GtLength h_k])]
        simp [List.Vector.length]
        have h_lt : (↑q * s[d] + i) * ((s.set k n).drop (d + 1)).prod + ↑r < (s.take k).prod * (n * (s.drop (k + 1)).prod) := by
          have h_prod_take' : ((s.set k n).take (d + 1)).prod = (s.take (d + 1)).prod := by
            simp [TakeSet.eq.Take.of.Ge (show k ≥ d + 1 by omega) n, ProdTake.eq.MulProdTake.of.GtLength h_d_length]
          have h_row₀ : (↑q * s[d] + ↑i) < (s.take (d + 1)).prod := by
            rw [ProdTake.eq.MulProdTake.of.GtLength h_d_length]
            apply AddMul.lt.Mul.of.Lt.Lt _ h_i
            rwa [← TakeSet.eq.Take.of.Ge (show k ≥ d by omega) n]
          have h_row : (↑q * s[d] + ↑i) < ((s.set k n).take (d + 1)).prod := Nat.lt_of_lt_of_eq h_row₀ h_prod_take'.symm
          have h_lt₀ := AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop (s := s.set k n) (d := d + 1) h_row h_r
          rwa [← ProdSet.eq.MulProd_Mul_Prod.of.GtLength (by omega) n]
        let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
        let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
        simp [GetResize.eq.Ite_Get_Mod.fin]
        split_ifs with h_rₐ? h_r'? h_s_d h_r' h_s_d
        ·
          omega
        ·
          simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          rw [GetCast.eq.Get.of.Eq.fin (by simp; grind)]
          have h_lt : ↑q' * ((s.eraseIdx d).drop (k - 1)).prod + ↑r' % ((s.eraseIdx d).drop (k - 1)).prod < ((⟨↑↑i, ↑(s.take (d + 1)).prod, ↑s[d]⟩ : Slice).length (s.take (d + 1)).prod) * (s.drop (d + 1)).prod := by
            simp [h_length_slice]
            rw [Prod.eq.MulProdS (s.eraseIdx d) (k - 1)]
            apply AddMul.lt.Mul.of.Lt.Lt q'.isLt
            apply LtMod.of.Gt_0
            grind
          let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
          let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
          erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₕrₕ]
          erw [GetGetSlice.eq.Get.of.GtGet.GtLength (by grind) (by grind)]
          erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          apply congrArg
          simp
          simp [EqAddSub.of.Ge (show k ≥ 1 by omega)] at h_r'_mod h_q'_div h_qₕ_div h_rₕ_mod
          simp [DropEraseIdx.eq.Drop.of.Le (show d ≤ k - 1 by omega)] at h_qₕ_div h_rₕ_mod h_q'_div
          simp [ProdDrop.eq.MulProdSDrop.of.Le (show d + 1 ≤ k by omega) s] at *
          simp [Div_Mul.eq.DivDiv.comm] at h_qₕ_div
          conv_rhs => rw [← ProdDrop.eq.MulProdSDrop.of.Le (show d + 1 ≤ k by omega)]
          rw [MulAdd.eq.AddMulS]
          simp [EqAddSub.of.Ge (show k ≥ 1 by omega)] at h_qₕ_div h_rₕ_mod
          rw [DropEraseIdx.eq.Drop.of.Le (show d ≤ k by omega)] at h_q'_div h_r'_mod
          rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₕ_div
          simp only [DivMod.eq.Zero] at h_qₕ_div
          simp at h_qₕ_div
          rw [Mod_Mul.eq.AddMul_Mod.of.Ne_0 (by grind)] at h_rₕ_mod
          rw [MulMul.eq.Mul_Mul]
          rw [Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength (by grind)]
          simp [ProdDropSet.eq.MulProdDropTake.of.Ge.GtLength h_k (show k ≥ d + 1 by omega) n] at h_qₐ_div h_rₐ_mod h_q_div h_r_mod
          simp [h_qₐ_div, h_rₐ_mod]
          rw [AddAdd.comm]
          rw [MulMul.eq.Mul_Mul (b := n)]
          rw [Mul_Mul.eq.MulMul]
          simp
          rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)]
          rw [MulAdd.eq.AddMulS]
          rw [MulMul.eq.Mul_Mul]
          rw [MulProdSDrop.eq.ProdDrop.of.Le (by omega)]
          rw [MulAdd.eq.AddMulS]
          conv_lhs =>
            arg 1
            rw [AddAdd.comm]
          rw [AddAdd.comm]
          congr 1
          simp [h_q_div, h_r_mod, h_q'_div, h_r'_mod, h_qₕ_div, h_rₕ_mod]
          rw [MulMul.rotate (b := n)]
          rw [ModMod_Mul.eq.Mod.left]
          rw [DivMod_Mul.eq.ModDiv]
          rw [MulMul.eq.Mul_Mul]
          rw [Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength h_d_length]
          rw [DivDiv.eq.Div_Mul]
          ring_nf
        ·
          obtain h_eq | h_div_mul_lt := Nat.eq_or_lt_of_le (Nat.div_mul_le_self (n * (s.drop (k + 1)).prod) (s.drop k).prod)
          ·
            exfalso
            simp only [DropEraseIdx.eq.Drop.of.Le (show d ≤ k - 1 by omega), DropEraseIdx.eq.Drop.of.Le (show d ≤ k by omega), show k - 1 + 1 = k by omega] at h_r'?
            have h_r'_lt : ↑r' < n * (s.drop (k + 1)).prod := by simpa [DropEraseIdx.eq.Drop.of.Le (show d ≤ k by omega), show k - 1 + 1 = k by omega] using r'.isLt
            exact h_r'? (Nat.lt_of_lt_of_eq h_r'_lt h_eq.symm)
          ·
            obtain h_prod_drop | h_prod_drop := Nat.eq_zero_or_pos (s.drop k).prod
            ·
              exfalso
              simp [h_prod_drop, Nat.div_zero] at *
            ·
              if hD1 : (s.drop k).prod = 1 then
                exfalso
                have h_threshold : n * (s.drop (k + 1)).prod / (s.drop k).prod * (s.drop k).prod = n * (s.drop (k + 1)).prod := by simp [hD1, Nat.div_one]
                simp [h_threshold, DropEraseIdx.eq.Drop.of.Le (show d ≤ k - 1 by omega), DropEraseIdx.eq.Drop.of.Le (show d ≤ k by omega), show k - 1 + 1 = k by omega] at h_r'?
                have h_r'_lt : ↑r' < n * (s.drop (k + 1)).prod := by simpa [DropEraseIdx.eq.Drop.of.Le (show d ≤ k by omega), show k - 1 + 1 = k by omega] using r'.isLt
                exact Nat.lt_irrefl r' (Nat.lt_of_lt_of_le h_r'_lt h_r'?)
              else
                exfalso
                have h_drop := ProdDropSet.eq.MulProdDropTake.of.Ge.GtLength h_k (show k ≥ d + 1 by omega) n
                have h_mod_eq : ((↑q * s[d] + ↑i) * ((s.set k n).drop (d + 1)).prod + ↑r) % (n * (s.drop (k + 1)).prod) = ↑t % (n * (s.drop (k + 1)).prod) := by
                  have h_sd := Nat.lt_of_le_of_lt (Nat.zero_le ↑i) h_i
                  have hdrop_le : ((s.set k n).drop (d + 1)).prod ≤ s[d] * ((s.set k n).drop (d + 1)).prod := by
                    calc
                      _ ≤ ((s.set k n).drop (d + 1)).prod * s[d] := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (Nat.ne_of_gt h_sd))
                      _ = s[d] * ((s.set k n).drop (d + 1)).prod := Nat.mul_comm _ _
                  have h_le : ↑t ≤ (↑q * s[d] + ↑i) * ((s.set k n).drop (d + 1)).prod + ↑r := by
                    rw [h_qr]
                    apply Nat.add_le_add_right
                    rw [Nat.add_mul]
                    apply Nat.le_trans _ (Nat.le_add_right _ _)
                    rw [Nat.mul_assoc]
                    exact Nat.mul_le_mul_left _ hdrop_le
                  have h_dvd : (n * (s.drop (k + 1)).prod) ∣ (↑q * s[d] + ↑i) * ((s.set k n).drop (d + 1)).prod + ↑r - ↑t := by
                    rw [h_qr]
                    have h_sub : (↑q * s[d] + ↑i) * ((s.set k n).drop (d + 1)).prod + ↑r - (↑q * ((s.set k n).drop (d + 1)).prod + ↑r) = (↑q * (s[d] - 1) + ↑i) * ((s.set k n).drop (d + 1)).prod := by
                      rw [Nat.add_mul]
                      rw [Nat.add_sub_add_right _ ↑r _]
                      rw [AddMulS.eq.MulAdd]
                      rw [SubMulS.eq.MulSub]
                      rw [SubAdd.eq.AddSub.of.Ge (GeMul.of.Gt_0 h_sd)]
                      grind
                    rw [h_sub]
                    rw [h_drop]
                    refine ⟨(↑q * (s[d] - 1) + ↑i) * ((s.take k).drop (d + 1)).prod, ?_⟩
                    ring_nf
                  rw [← Nat.add_sub_of_le h_le]
                  rw [Nat.add_mod]
                  rw [Nat.mod_eq_zero_of_dvd h_dvd]
                  rw [Nat.add_zero, Nat.mod_mod]
                simp only [DropEraseIdx.eq.Drop.of.Le (show d ≤ k - 1 by omega), DropEraseIdx.eq.Drop.of.Le (show d ≤ k by omega), show k - 1 + 1 = k by omega] at h_rₐ? h_r'? h_rₐ_mod h_r'_mod
                rw [h_rₐ_mod, h_mod_eq] at h_rₐ?
                rw [h_r'_mod] at h_r'?
                exact h_r'? h_rₐ?
        ·
          grind
        ·
          obtain hB0 | hBpos := Nat.eq_zero_or_pos ((s.eraseIdx d).drop (k - 1)).prod
          ·
            exfalso
            simp [hB0, Nat.div_zero] at *
          ·
            obtain h_prod_drop | h_prod_drop := Nat.eq_zero_or_pos (s.drop k).prod
            ·
              exfalso
              simp [h_prod_drop, Nat.div_zero] at *
              sorry
            ·
              if hD1 : (s.drop k).prod = 1 then
                simp [hD1, Nat.div_one] at *
              else
                obtain h_eq | h_div_mul_lt := Nat.eq_or_lt_of_le (Nat.div_mul_le_self (n * (s.drop (k + 1)).prod) (s.drop k).prod)
                ·
                  grind
                ·
                  sorry
        ·
          rfl
      ·
        simp
        rw [h_length_slice]
        rw [EraseIdxSet.eq.SetEraseIdx.of.Gt h_d]
        rw [h_prod_set]


-- created on 2026-07-30
-- updated on 2026-08-01
