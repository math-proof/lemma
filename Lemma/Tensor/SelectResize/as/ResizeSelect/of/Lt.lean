import Lemma.List.AddMul_ProdDrop.lt.ProdDrop.of.GtProdDrop_Succ.GtGet.Gtlength
import Lemma.List.ProdDrop.eq.MulProdDrop_Add_1.of.GtLength
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
import Lemma.Nat.Add_Add
import Lemma.Nat.Mul_Add.eq.AddMulS
import Lemma.Nat.Mul_Mul
import Lemma.Nat.DivMod.eq.Zero
import Lemma.Nat.ModMod_Mul.eq.Mod
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
set_option maxHeartbeats 16000000


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
        let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        have h_q := q.isLt
        have h_r := r.isLt
        have h_s := LengthSet.eq.Length s k n
        have h_d_lt_length := h_d
        simp only [← h_s] at h_d_lt_length
        have h_length_slice' := LengthSlice.eq.ProdTake.of.GtGet.GtLength (i := i) h_d_lt_length (show ↑i < (s.set k n)[d.val] by grind)
        rw [List.ProdTakeMapCast.eq.ProdTake] at h_length_slice'
        simp only [h_length_slice'] at h_q
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
        let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
        let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
        simp
        erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
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
          let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
          let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
          erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₕrₕ]
          erw [Vector.GetGetSlice.eq.Get.of.GtGet.GtLength (by grind) (by grind)]
          erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          apply congrArg
          simp
          have h_k' := Le.of.Lt h_k
          rw [ModAdd.eq.Mod.of.Dvd.left (Dvd_Mul.of.Dvd (ProdDrop.dvd.ProdDropEraseIdx.of.Ge h_k' s) q')] at h_rₕ_mod
          simp [ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge h_k'] at h_qₕ_div h_rₕ_mod h_q'_div h_r'_mod h_t
          rw [Mul_Mul.eq.MulMul] at h_qₕ_div
          rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₕ_div
          simp [h_rₕ_mod]
          simp [DropSet.eq.Drop.of.Lt (show k < d + 1 by omega)] at h_qₐ_div h_rₐ_mod h_q_div h_r_mod h_r
          simp [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ d by omega) s] at *
          rw [MulAdd.eq.AddMulS, MulMul.eq.Mul_Mul] at h_qₐ_div h_rₐ_mod ⊢
          rw [Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength h_d] at h_qₐ_div h_rₐ_mod ⊢
          have h_prod_drop := ProdDrop.eq.MulProdSDrop.of.Le (i := k) (j := d) (by omega) s
          simp [Mul_Mul.eq.MulMul, Div_Mul.eq.DivDiv.comm] at h_qₐ_div
          rw [AddAdd.comm] at h_qₐ_div
          conv at h_qₐ_div =>
            rhs
            arg 1
            arg 1
            arg 1
            rw [AddAdd.eq.Add_Add]
          conv at h_qₐ_div =>
            rhs
            arg 1
            arg 1
            rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)]
          rw [Div.eq.Zero.of.Lt (n := (s.drop d).prod)] at h_qₐ_div
          ·
            simp [DivDiv.eq.Div_Mul.comm] at h_qₐ_div
            have h_rₐ_mod := h_rₐ_mod
            rw [Mul_Mul.eq.MulMul] at h_rₐ_mod
            rw [AddAdd.eq.Add_Add] at h_rₐ_mod
            have h_r := r.isLt
            have h_q := h_q
            simp [List.DropSet.eq.Drop.of.Lt (show d + 1 > k by grind)] at h_r
            have h_lt_ir := AddMul_ProdDrop.lt.ProdDrop.of.GtProdDrop_Succ.GtGet.Gtlength h_d i.isLt h_r
            rw [Nat.Mod_Mul.eq.AddMul_Mod.of.Lt h_lt_ir] at h_rₐ_mod
            simp [h_qₐ_div, h_rₐ_mod]
            have h_qₕ_div := h_qₕ_div
            have h_rₕ_mod := h_rₕ_mod
            conv_rhs => rw [AddAdd.comm]
            sorry
            rw [AddAdd.comm]
            congr 1
            ·
              simp [h_q_div, h_q'_div, h_qₕ_div, Div_Mul.eq.DivDiv.comm, ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show ↑d ≥ k + 1 by omega)]
              rw [DivDiv.eq.Div_Mul]
              ring_nf
              grind
            ·
              rw [MulAdd.eq.AddMulS]
              rw [MulProdSDrop.eq.ProdDrop.of.Le (show k + 1 ≤ d by omega)]
              rw [MulAdd.eq.AddMulS]
              simp [h_q_div, h_r_mod, h_q'_div, h_r'_mod, h_qₕ_div, h_rₕ_mod]
              rw [MulMul.rotate (b := n)]
              rw [ModMod_Mul.eq.Mod.left]
              rw [DivMod_Mul.eq.ModDiv]
              rw [MulMul.eq.Mul_Mul]
              rw [Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength h_d]
              rw [Mod_Mul.eq.AddMul_Mod.of.Ne_0 (by grind)]
              rw [Mod_Mul.eq.AddMul_Mod.of.Lt i.isLt]
              rw [MulAdd.eq.AddMulS]
              simp [Mul.comm (b := (s.drop (d + 1)).prod)]
              rw [DivDiv.eq.Div_Mul]
              ring_nf
          ·
            rw [← Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength h_d]
            have h_lt' := AddMul.lt.Mul.of.Lt.Lt i.isLt h_r
            rwa [Add.comm]
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
