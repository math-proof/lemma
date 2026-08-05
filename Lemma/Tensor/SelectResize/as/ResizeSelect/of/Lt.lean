import Lemma.Nat.LeMulS.of.Le
import Lemma.Nat.ModEq.of.ModEqMul
import Lemma.Nat.ModAdd_Mul.eq.Mod
import Lemma.Nat.Mod.of.Eq
import Lemma.Nat.ModMod_Mul.eq.Mod
import Lemma.Nat.ModEq.of.EqMod
import Lemma.Nat.ModEq.of.AddMul
import Lemma.Nat.ModEq.of.EqAddMul
import Lemma.Nat.MulDiv.eq.Sub_Mod
import Lemma.Nat.DivMulS.eq.Div.of.Ne_0
import Lemma.List.AddMul_ProdDrop.lt.ProdDrop.of.GtProdDrop_Succ.GtGet.Gtlength
import Lemma.List.ProdDrop.eq.MulProdDrop_Add_1.of.GtLength
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.ProdTakeSet.eq.MulProdSetTake.of.Ne.GtLength
import Lemma.Nat.Ne.of.Lt
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
import Lemma.List.ProdDropTake.eq.MulProdDropTake.of.Gt.GtLength
import Lemma.List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge
import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.AddMul_ProdDrop.lt.Prod
import Lemma.List.Mod_Mul.lt.MulDiv.of.Lt_Mul.Lt
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
import Lemma.Nat.Lt.of.Lt.Lt
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.ModAdd.eq.Mod.of.Dvd
import Lemma.Nat.DivMod_Mul.eq.ModDiv
import Lemma.Nat.Eq.Eq.of.AddMul.Lt.Lt
import Lemma.Nat.Mod_Mul.eq.AddMul_Mod.of.Lt
import Lemma.Nat.Mod_Mul.eq.AddMul_Mod.of.Ne_0
import Lemma.Nat.Mul
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulDivMul.eq.Mul
import Lemma.Nat.MulDivMulS.eq.Mul_MulDivMulS
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
        have h_d_lt_length := d.isLt
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
        simp [GetSet.eq.Get.of.Lt.GtLength d.isLt h_k]
        rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
        simp [DataResize.eq.Cast_FlattenMapSplitAtData]
        have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength (s := s) (d := d) (i := i) (by grind) (by grind)
        rw [List.ProdTakeMapCast.eq.ProdTake] at h_length_slice
        rw [GetCast.eq.Get.of.Eq.fin (by simp [ProdSet.eq.MulProd_Mul_Prod.of.GtLength (Lt.of.Lt.Lt h_k d.isLt)])]
        have h_lt : (↑q * s[↑d] + ↑i) * ((s.set k n).drop (↑d + 1)).prod + ↑r < (s.take k).prod * (n * (s.drop (k + 1)).prod) := by
          rw [MulProd_Mul_Prod.eq.ProdSet.of.GtLength (by grind) n]
          apply AddMul_ProdDrop.lt.Prod.of.Lt_ProdTake.Lt_ProdDrop _ h_r
          apply Nat.lt_of_lt_of_eq _ (MulProdSetTake.eq.ProdTakeSet.of.Ne.GtLength d.isLt (Ne.of.Lt h_k) n)
          apply AddMul.lt.Mul.of.Lt.Lt _ i.isLt
          rwa [TakeSet.eq.SetTake.of.Lt h_k] at h_q
        let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
        let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
        simp
        erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
        simp [GetResize.eq.Ite_Get_Mod.fin]
        simp only [DropSet.eq.Drop.of.Lt (show k < d + 1 by omega)] at h_rₐ_mod h_r'_mod
        rw [MulAdd.eq.AddMulS] at h_qₐrₐ
        simp only [DropSet.eq.Drop.of.Lt (show k < d + 1 by omega)] at h_qₐrₐ h_q'r' h_r'_mod
        simp only [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ d by omega) s, ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k + 1 by grind)] at h_qₐrₐ h_q'r' h_r'_mod
        rw [AddMulS.eq.MulAdd] at h_qₐrₐ
        conv_rhs at h_qₐrₐ =>
          arg 1; arg 2; arg 2; arg 2
          rw [← Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength d.isLt]
        have h_rhs : ↑qₐ * (n * (((s.take ↑d).drop (k + 1)).prod * (s[↑d] * (s.drop (↑d + 1)).prod))) + ↑rₐ = (↑qₐ * n * ((s.take ↑d).drop (k + 1)).prod * s[↑d]) * (s.drop (↑d + 1)).prod + ↑rₐ := by
          ring_nf
        have h_mod_r := ModEq.of.AddMul (h_qₐrₐ.trans h_rhs)
        have h_mod_r' := ModEq.of.Eq_AddMul h_q'r'
        have h_mod_qr := ModEq.of.Eq_AddMul (by simpa [DropSet.eq.Drop.of.Lt (show k < d + 1 by omega)] using h_qr)
        have h_mod := h_mod_qr.trans h_mod_r
        simp only [ModEq] at h_mod h_mod_r' h_mod_r
        have h_T_threshold : n * (((s.take ↑d).drop (k + 1)).prod * (s.drop ↑d).prod) / (s.drop k).prod * (s.drop k).prod = s[↑d] * (n * (((s.take ↑d).drop (k + 1)).prod * (s.drop (↑d + 1)).prod) / ((s.eraseIdx ↑d).drop k).prod * ((s.eraseIdx ↑d).drop k).prod) := by
          simp only [ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k by omega)]
          rw [ProdDrop.eq.MulProdSDrop.of.Le (show k ≤ ↑d by omega) s]
          rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength d.isLt]
          have h_take_drop : ((s.take ↑d).drop k).prod = ((s.take ↑d).drop (k + 1)).prod * s[k] := by
            rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength (by simp; grind)]
            rw [List.GetTake.eq.Get.of.GtLengthTake (by grind)]
            grind
          rw [h_take_drop]
          conv_lhs =>
            arg 1; arg 1; arg 2
            rw [← Nat.mul_assoc, Nat.mul_comm (n := ((s.take ↑d).drop (k + 1)).prod), Nat.mul_assoc]
          conv_lhs =>
            arg 1; arg 2
            rw [MulMul.eq.Mul_Mul.swap]
          conv_lhs =>
            arg 1; arg 2; arg 2
            rw [← Nat.mul_assoc, Nat.mul_comm (n := ((s.take ↑d).drop (k + 1)).prod), Nat.mul_assoc]
          conv_lhs =>
            arg 2
            rw [MulMul.eq.Mul_Mul.swap]
          conv_lhs =>
            arg 2; arg 2
            rw [← Nat.mul_assoc, Nat.mul_comm (n := ((s.take ↑d).drop (k + 1)).prod), Nat.mul_assoc]
          conv_rhs =>
            arg 2; arg 1; arg 2
            rw [MulMul.eq.Mul_Mul.swap]
          conv_rhs =>
            arg 2; arg 2
            rw [MulMul.eq.Mul_Mul.swap]
          apply MulDivMulS.eq.Mul_MulDivMulS
        split_ifs with h_rₐ? h_r'_if h_r'_if'
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
          simp [ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge h_k'] at h_qₕ_div h_rₕ_mod h_q'_div h_r'_mod
          simp [ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k + 1 by grind)] at h_q'_div h_r'_mod
          rw [Mul_Mul.eq.MulMul] at h_qₕ_div
          rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₕ_div
          simp [h_rₕ_mod]
          simp [DropSet.eq.Drop.of.Lt (show k < d + 1 by omega)] at h_qₐ_div h_rₐ_mod h_q_div h_r_mod h_r
          simp [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ d by omega) s] at h_qₐ_div h_rₐ_mod
          rw [MulAdd.eq.AddMulS, MulMul.eq.Mul_Mul] at h_qₐ_div h_rₐ_mod ⊢
          rw [Mul_ProdDrop_Add_1.eq.ProdDrop.of.GtLength d.isLt] at h_qₐ_div h_rₐ_mod ⊢
          simp [Mul_Mul.eq.MulMul, Div_Mul.eq.DivDiv.comm] at h_qₐ_div
          rw [AddAdd.comm] at h_qₐ_div
          conv at h_qₐ_div =>
            rhs
            arg 1
            arg 1
            arg 1
            rw [AddAdd.eq.Add_Add]
          have h_lt_ir := AddMul_ProdDrop.lt.ProdDrop.of.GtProdDrop_Succ.GtGet.Gtlength d.isLt i.isLt h_r
          conv at h_qₐ_div =>
            rhs
            arg 1
            arg 1
            rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)]
          rw [Div.eq.Zero.of.Lt (n := (s.drop d).prod) (by grind)] at h_qₐ_div
          simp [DivDiv.eq.Div_Mul.comm] at h_qₐ_div
          rw [Mul_Mul.eq.MulMul] at h_rₐ_mod
          rw [AddAdd.eq.Add_Add] at h_rₐ_mod
          rw [Nat.Mod_Mul.eq.AddMul_Mod.of.Lt h_lt_ir] at h_rₐ_mod
          simp [h_qₐ_div, h_rₐ_mod]
          conv_rhs => rw [AddAdd.comm]
          rw [ProdDrop.eq.MulProdSDrop.of.Le (i := k) (j := d) (by omega)]
          rw [List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength (show (s.take ↑d).length > k by grind)]
          rw [List.GetTake.eq.Get.of.GtLengthTake (by grind)]
          rw [Nat.Mod_Mul.eq.AddMul_Mod.of.Lt h_lt_ir]
          rw [Add_Add.eq.AddAdd]
          rw [Add_Add.eq.AddAdd]
          rw [AddAdd.eq.Add_Add]
          rw [Add_Add.eq.AddAdd]
          rw [AddAdd.comm]
          congr 1
          simp [h_q_div, h_r_mod, h_q'_div, h_r'_mod, h_qₕ_div]
          rw [MulAdd.eq.AddMulS]
          simp [Mul_Mul.eq.MulMul, Div_Mul.eq.DivDiv.comm]
          rw [List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength (s := s.take ↑d) (i := k) (by grind)]
          rw [List.GetTake.eq.Get.of.GtLengthTake (by grind)]
          congr 1
          ·
            ring_nf
          ·
            conv_rhs => rw [MulMul.eq.Mul_Mul.permute (a := s[k])]
            rw [DivMod_Mul.eq.ModDiv]
            rw [MulMul.eq.Mul_Mul.permute]
            rw [DivMod_Mul.eq.ModDiv]
        ·
          simp [List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k + 1 by grind)] at h_r'_if
          simp [List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k by grind)] at h_r'_if
          simp [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ d by omega) s] at h_rₐ?
          simp [ProdDrop.eq.MulProdSDrop.of.Le (show k ≤ d by omega) s] at h_rₐ?
          rw [List.ProdDrop.eq.MulProdDrop_Add_1.of.GtLength d.isLt] at h_rₐ?
          rw [Mul_Mul.eq.MulMul (c := s[d.val]), Mul_Mul.eq.MulMul (c := s[d.val]), Mul_Mul.eq.MulMul (c := s[d.val]), Mul_Mul.eq.MulMul (c := s[d.val])] at h_rₐ?
          rw [Nat.DivMulS.eq.Div.of.Ne_0 (by grind)] at h_rₐ?
          have h_r' := LeMulS.of.Le h_r'_if s[d]
          have h_lt := Nat.Lt.of.Lt.Le h_rₐ? h_r'
          rw [h_rₐ_mod] at h_lt
          rw [h_r'_mod] at h_lt
          simp only [DropSet.eq.Drop.of.Lt (show k < ↑d + 1 by omega)] at h_qr
          rw [h_qr] at h_lt
          have h_mod_r'ₐ : ↑r' % (s.drop (↑d + 1)).prod = ↑rₐ % (s.drop (↑d + 1)).prod := by
            set D := (s.drop (↑d + 1)).prod
            set M := n * (((s.take ↑d).drop (k + 1)).prod * D)
            have h_mod_r'_eq : ↑r' % M = ↑t % M := h_mod_r'.symm
            calc
              _ = ↑r' % M % D := by
                unfold M
                conv_rhs =>
                  arg 1; arg 2
                  rw [show n * (((s.take ↑d).drop (k + 1)).prod * D) = n * ((s.take ↑d).drop (k + 1)).prod * D by ring_nf]
                rw [← ModMod_Mul.eq.Mod (k := ↑r') (m := n * ((s.take ↑d).drop (k + 1)).prod) (n := D)]
              _ = ↑t % M % D := congrArg (fun x => x % D) h_mod_r'_eq
              _ = ↑t % D := by
                unfold M
                rw [← show (n * ((s.take ↑d).drop (k + 1)).prod) * D = n * (((s.take ↑d).drop (k + 1)).prod * D) by ring_nf, ← ModMod_Mul.eq.Mod (k := ↑t) (m := n * ((s.take ↑d).drop (k + 1)).prod) (n := D)]
              _ = ↑rₐ % D := h_mod
          rw [h_r'_mod] at h_r'
          set M := n * (((s.take ↑d).drop (k + 1)).prod * (s.drop (↑d + 1)).prod) with h_M
          have h_lhs : ((↑q * s[↑d] + ↑i) * (s.drop (↑d + 1)).prod + ↑r) = (↑qₐ * s[↑d]) * M + ↑rₐ := by
            refine (h_qₐrₐ.trans h_rhs).trans ?_
            unfold M
            ring_nf
          have hM_pos : 0 < M := by unfold M; grind
          have h_M_sd : M * s[↑d] = n * (s.drop (k + 1)).prod := by
            unfold M
            rw [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ ↑d + 1 by omega) s]
            rw [ProdDropTake.eq.MulProdDropTake.of.Gt.GtLength d.isLt h_k]
            ac_rfl
          have h_lhs_side : ((↑q * s[↑d] + ↑i) * (s.drop (↑d + 1)).prod + ↑r) % (M * s[↑d]) = ↑rₐ := by
            rw [show M * s[d] = n * (s.drop (k + 1)).prod from h_M_sd]
            exact h_rₐ_mod.symm
          have h_lt_r' : ↑r' < M := by rw [h_r'_mod]; exact Nat.mod_lt _ hM_pos
          have h_t_side : ↑t % (M * s[↑d]) = ↑q' % s[↑d] * M + ↑r' := by
            rw [h_q'r', ← Nat.mul_comm s[d] M, Mod_Mul.eq.AddMul_Mod.of.Lt h_lt_r']
          have h_r'' : ↑r' < n * (((s.take ↑d).drop (k + 1)).prod * (s.drop (↑d + 1)).prod) / (((s.take ↑d).drop k).prod * (s.drop (↑d + 1)).prod) * (((s.take ↑d).drop k).prod * (s.drop (↑d + 1)).prod) := by
            rw [← h_M]
            by_cases h : n % s[k] = 0
            ·
              have hT_eq_M :
                  M / (((s.take ↑d).drop k).prod * (s.drop (↑d + 1)).prod) * (((s.take ↑d).drop k).prod * (s.drop (↑d + 1)).prod) = M := by
                rw [h_M]
                have h_take_drop : ((s.take ↑d).drop k).prod = ((s.take ↑d).drop (k + 1)).prod * s[k] := by
                  rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength (by simp; grind)]
                  rw [List.GetTake.eq.Get.of.GtLengthTake (by grind)]
                  grind
                rw [h_take_drop]
                conv_lhs =>
                  arg 1; arg 1
                  rw [show n * (((s.take ↑d).drop (k + 1)).prod * (s.drop (↑d + 1)).prod) =
                      (n / s[k]) * (((s.take ↑d).drop (k + 1)).prod * s[k] * (s.drop (↑d + 1)).prod) by
                    rw [← Nat.mul_assoc, ← EqMulDiv.of.Dvd (Nat.dvd_of_mod_eq_zero h)]
                    ring_nf]
                rw [MulDivMul.eq.Mul]
                rw [← Nat.mul_assoc, ← EqMulDiv.of.Dvd (Nat.dvd_of_mod_eq_zero h)]
                ac_rfl
              rw [hT_eq_M]
              exact h_lt_r'
            ·
              refine Nat.not_le.mp ?_
              intro hle
              rw [h_lhs_side, h_q_div, h_r_mod, h_rₐ_mod, h_r'_mod, h_M_sd] at h_lt
              grind
          simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin, h_r'', h_mod_r'ₐ, h_lt]
          grind
        ·
          simp [List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k + 1 by grind)] at h_r'_if
          simp [List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k by grind)] at h_r'_if
          simp [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ d by omega) s] at h_rₐ?
          simp [ProdDrop.eq.MulProdSDrop.of.Le (show k ≤ d by omega) s] at h_rₐ?
          rw [List.ProdDrop.eq.MulProdDrop_Add_1.of.GtLength d.isLt] at h_rₐ?
          rw [Mul_Mul.eq.MulMul (c := s[d.val]), Mul_Mul.eq.MulMul (c := s[d.val]), Mul_Mul.eq.MulMul (c := s[d.val]), Mul_Mul.eq.MulMul (c := s[d.val])] at h_rₐ?
          rw [Nat.DivMulS.eq.Div.of.Ne_0 (by grind)] at h_rₐ?
          have h_r' := Nat.not_le.mp h_r'_if
          have h_lt := Nat.Lt.of.Lt.Le h_rₐ? h_r'
          rw [h_rₐ_mod] at h_lt
          rw [h_r_mod] at h_lt
          simp only [DropSet.eq.Drop.of.Lt (show k < ↑d + 1 by omega)] at h_qr
          rw [h_qr] at h_lt
          simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          grind
        ·
          rfl
      ·
        simp [h_length_slice]
        rw [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k]
        rw [h_prod_set]


-- created on 2026-07-30
