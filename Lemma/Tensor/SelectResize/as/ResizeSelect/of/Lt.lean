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
import Lemma.List.ProdCons.eq.Mul_Prod
import Lemma.List.ProdDrop.dvd.ProdDropEraseIdx.of.Ge
import Lemma.List.ProdDrop.eq.MulProdSDrop.of.Le
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge
import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.List.ProdTakeDrop.eq.MulProdTakeDrop.of.GtLength
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.List.TakeDrop.eq.Cons_TakeDrop.of.GtLength
import Lemma.List.TakeDrop.eq.DropTake
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
set_option maxHeartbeats 2000000


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
  have h_get_eraseIdx := GetEraseIdx.eq.Get.of.Gt.GtLength h_d h_k
  apply SEq.of.SEqDataS.Eq
  ·
    simp [h_get_eraseIdx]
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
        repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        simp [GetSet.eq.Get.of.Lt.GtLength h_d h_k]
        simp [DataSelect.eq.Cast_FlattenGetSliceSplitAtData]
        simp [DataResize.eq.Cast_FlattenMapSplitAtData]
        have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength (s := s) (d := d) (i := i) (by grind) (by grind)
        rw [List.ProdTakeMapCast.eq.ProdTake] at h_length_slice
        repeat rw [GetCast.eq.Get.of.Eq.fin]
        ·
          have h_prod_take := ProdTake.eq.MulProdTake.of.GtLength h_d
          have h_prod_take_d :=
            ProdSet.eq.MulProd_Mul_Prod.of.GtLength (s := s.take d) (i := k) (by simp; grind) n
          have h_cons : ((s.take d).drop k).prod = s[k] * ((s.take d).drop (k + 1)).prod := by
            have h := ProdTakeDrop.eq.MulProdTakeDrop.of.GtLength (s := s) (i := k) (h := by omega) (d := d - k - 1)
            rw [show d - k - 1 + 1 = d - k from by omega] at h
            have h1 : (s.take d).drop k = (s.drop k).take (d - k) :=
              by simpa [show k + (d - k) = d by omega] using (TakeDrop.eq.DropTake (s := s) (i := k) (j := d - k)).symm
            have h2 : (s.take d).drop (k + 1) = (s.drop (k + 1)).take (d - k - 1) :=
              by simpa [show k + 1 + (d - k - 1) = d by omega] using (TakeDrop.eq.DropTake (s := s) (i := k + 1) (j := d - k - 1)).symm
            simpa [h1, h2, Mul.comm] using h
          have h_prod_split : (s.take d).prod = (s.take k).prod * ((s.take d).drop k).prod := by
            rw [Prod.eq.MulProdS (s.take d) k]
            congr 1
            grind
          have h_lt : (↑q * s[d] + i) * ((s.set k n).drop (d + 1)).prod + ↑r < (s.take k).prod * (n * (s.drop k).prod) := by
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
            rw [h_prod_take_d] at h_q
            have h_take : (s.take d).take k = s.take k := by grind
            rw [h_take] at h_q
            rw [h_prod_split, h_cons]
            grind
          let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
          let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
          have h_lt : ↑q' * ((s.eraseIdx d).drop k).prod + ↑r' % ((s.eraseIdx d).drop k).prod < (⟨↑i, ↑(s.take (d + 1)).prod, s[d.val]⟩ : Slice).length (s.take (d + 1)).prod * (s.drop (d + 1)).prod := by
            rw [h_length_slice]
            rw [Prod.eq.MulProdS (s.eraseIdx d) k]
            apply AddMul.lt.Mul.of.Lt.Lt q'.isLt
            exact LtMod.of.Gt_0 (by grind)
          let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
          have h_qₑ := qₑ.isLt
          let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
          repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
          rw [GetGetSlice.eq.Get.of.GtGet.GtLength h_d i.isLt]
          simp [GetResize.eq.Ite_Get_Mod.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          split_ifs
          ·
            apply congrArg
            simp
            have h_k' := Le.of.Lt h_k
            rw [ModAdd.eq.Mod.of.Dvd.left (Dvd_Mul.of.Dvd (ProdDrop.dvd.ProdDropEraseIdx.of.Ge h_k' s) q')] at h_rₑ_mod
            simp [ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge h_k'] at h_qₑ_div h_rₑ_mod h_q'_div h_r'_mod h_t
            rw [Mul_Mul.eq.MulMul] at h_qₑ_div
            rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₑ_div
            simp [h_rₑ_mod]
            simp [DropSet.eq.Drop.of.Lt (show k < d + 1 by omega)] at h_qₐ_div h_rₐ_mod h_q_div h_r_mod h_r
            rw [MulAdd.eq.AddMulS, MulMul.eq.Mul_Mul] at h_qₐ_div h_rₐ_mod ⊢
            rw [Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength] at h_qₐ_div h_rₐ_mod ⊢
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
              rw [h_prod_drop]
              simp [Div_Mul.eq.DivDiv.comm]
              simp [AddAdd.eq.Add_Add]
              simp [Mul_Mul.eq.MulMul]
              rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength h_d]
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
              rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength h_d]
              apply AddMul.lt.Mul.of.Lt.Lt h_i h_r
          ·
            simp
            grind
        ·
          simp [ProdSet.eq.MulProd_Mul_Prod.of.GtLength (Lt.of.Lt.Lt h_k h_d)]
      ·
        simp [h_length_slice]
        rw [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k]
        rw [h_prod_set]


-- created on 2026-07-30
