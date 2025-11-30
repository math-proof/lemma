import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Int.OfNat.eq.Cast
import Lemma.List.DropLast.eq.Take_SubLength_1
import Lemma.List.EqPermute__0
import Lemma.List.GetPermute__Neg.eq.Get.of.GtLength
import Lemma.List.LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.Permute__Neg.eq.Rotate_SubLength_1.of.GtLength_0
import Lemma.List.Prod.eq.Mul_ProdDropLast.of.GtLength_0
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdDrop.eq.Get.of.GtLength_0
import Lemma.List.ProdDropTake.eq.Get.of.GtLength
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.List.ProdPermute.eq.Prod
import Lemma.List.ProdRotate.eq.MulProdS.of.GtLength
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTake.eq.DivProdTake.of.Ne_0.GtLength
import Lemma.List.ProdTake.eq.Mul_ProdTake.of.GtLength
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TailPermute.eq.EraseIdx
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Gt_0
import Lemma.Nat.LtDiv.of.Lt_Mul
import Lemma.Nat.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.LengthPermute.eq.Get
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat List Vector Bool Int Tensor


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  X.select d i ≃ (X.permute d (-d)).get ⟨i, by simp [LengthPermute.eq.Get]⟩ := by
-- proof
  apply SEq.of.SEqDataS.Eq
  ·
    apply EraseIdx.eq.TailPermute
  ·
    have h_s := Gt_0 d
    rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData]
    rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨i, by simp [GetPermute__Neg.eq.Get.of.GtLength d.isLt]⟩) (by simpa)]
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength]
    ·
      simp
    ·
      simp
      apply SEq.of.All_EqGetS.Eq.fin
      ·
        intro t
        have h_t := t.isLt
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        simp at h_t
        rw [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength (by omega) (by omega)] at h_t
        have h_q := q.isLt
        simp at h_q
        rw [LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength (by omega) (by omega)] at h_q
        have h_r := r.isLt
        let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
        rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin]
        ·
          have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
          rw [Add.comm] at h_toNat
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp [TailPermute.eq.EraseIdx]
          simp [@Tensor.Permute.eq.Ite]
          split_ifs with h_d0 h_neg h_end
          ·
            simp [h_d0]
            rw [DataCast.eq.Cast_Data.of.Eq]
            ·
              rw [GetCast.eq.Get.of.Eq.fin]
              ·
                apply congrArg
                simp [h_d0] at h_q h_r
                simp [h_q] at ⊢ h_qr
                exact h_qr.symm
              ·
                rw [ProdPermute.eq.Prod]
            ·
              simp [h_d0]
              rw [EqPermute__0]
          ·
            omega
          ·
            have h_d_succ : d + 1 = s.length := by omega
            have h_s : s.take (s.length - (1 - (-d : ℤ)).toNat) ++ (s.drop (s.length - (1 - (-d : ℤ)).toNat)).rotate ((1 - (-d : ℤ)).toNat ⊓ s.length - 1) = s.permute d (-d) := by
              simp only [h_toNat]
              simp [h_d_succ]
              simp [h_end]
              rw [Rotate_SubLength_1.eq.Permute__Neg.of.GtLength_0]
              ·
                simp [← h_end]
              ·
                linarith [d.isLt]
            rw [DataCast.eq.Cast_Data.of.Eq h_s]
            unfold permuteTail
            repeat rw [GetCast.eq.Get.of.Eq.fin]
            ·
              simp
              simp [h_end] at h_t
              rw [DropLast.eq.Take_SubLength_1] at h_t
              have h_lt : ↑i * (s.eraseIdx ↑d).prod + ↑t < (s.take (s.length - (1 - (-d : ℤ)).toNat)).prod * ((s.drop (s.length - (1 - (-d : ℤ)).toNat)).rotate ((1 - (-d : ℤ)).toNat ⊓ s.length - 1)).prod := by
                simp only [h_toNat]
                simp [h_d_succ]
                simp [h_end]
                rw [ProdRotate.eq.MulProdS.of.GtLength (by omega)]
                rw [DropLast.eq.Take_SubLength_1]
                apply AddMul.lt.Mul.of.Lt.Lt _ h_t
                rw [ProdDrop.eq.Get.of.GtLength_0 (by omega)]
                grind
              let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
              have h_q' := q'.isLt
              have h_r' := r'.isLt
              let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
              unfold Tensor.rotate
              simp
              rw [GetCast.eq.Get.of.Eq.fin]
              ·
                simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_r'
                let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r'
                let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
                rw [GetTranspose.eq.Get.fin]
                repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                simp only [h_toNat] at *
                apply congrArg
                simp [h_d_succ] at *
                simp [EqMod_1'0] at h_r_mod
                simp [h_q_div, h_r_mod]
                simp [h_end] at ⊢ h_q'_div h_r'_mod
                rw [ProdDrop.eq.Get.of.GtLength_0 (by omega)]
                simp [h_rₐ_mod]
                simp [ProdRotate.eq.Prod] at h_q'_div h_r'_mod
                rw [Take_SubLength_1.eq.DropLast] at ⊢ h_t h_qₐ_div
                have h_lt : ↑i * s.dropLast.prod + ↑t < s.prod := by
                  rw [Prod.eq.Mul_ProdDropLast.of.GtLength_0 (s := s) (by omega)]
                  apply AddMul.lt.Mul.of.Lt.Lt (by grind) h_t
                rw [EqMod.of.Lt h_lt] at h_r'_mod
                simp [h_q'_div, h_r'_mod]
                simp [h_r'_mod] at h_qₐ_div
                simp [EqMod.of.Lt h_t]
                simp [Div.eq.Zero.of.Lt h_lt]
                simp [h_qₐ_div]
                rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)]
                simp [Div.eq.Zero.of.Lt h_t]
              ·
                rw [MulProdS.eq.ProdAppend]
                rw [Rotate.eq.AppendDrop__Take]
            ·
              rw [MulProdS.eq.ProdAppend]
            ·
              rw [h_s]
          ·
            have h_d_succ : d + 1 ≤ s.length := by omega
            simp
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              simp
              have h_lt : ↑i * (s.eraseIdx ↑d).prod + ↑t < ((s.take (↑d + 1)).take ((s.take (↑d + 1)).length - (1 - (-d : ℤ)).toNat) ++ ((s.take (↑d + 1)).drop ((s.take (↑d + 1)).length - (1 - (-d : ℤ)).toNat)).rotate ((1 - (-d : ℤ)).toNat ⊓ (s.take (↑d + 1)).length - 1)).prod * (s.drop (↑d + 1)).prod := by
                simp only [h_toNat]
                simp [EqMin.of.Le h_d_succ]
                simp [ProdRotate.eq.Prod]
                rw [Mul.comm (b := s[d.val])]
                rw [MulMul.eq.Mul_Mul]
                rw [← ProdEraseIdx.eq.MulProdS]
                apply AddMul.lt.Mul.of.Lt.Lt i.isLt h_t
              let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
              have h_q' := q'.isLt
              have h_r' := r'.isLt
              let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
              unfold Tensor.permuteTail
              simp
              rw [GetCast.eq.Get.of.Eq.fin]
              ·
                simp only [ProdAppend.eq.MulProdS] at h_q'
                let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q'
                have h_qₐ := qₐ.isLt
                simp only [h_toNat] at h_qₐ
                simp at h_qₐ
                have h_rₐ := rₐ.isLt
                let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
                simp [h_qₐ] at h_qₐrₐ
                simp
                unfold Tensor.rotate
                simp
                rw [GetCast.eq.Get.of.Eq.fin]
                ·
                  simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_rₐ
                  let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_rₐ
                  let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₑrₑ]
                  rw [GetTranspose.eq.Get.fin]
                  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                  simp only [h_toNat] at ⊢ h_qₑ_div h_rₑ_mod
                  simp [EqMin.of.Le h_d_succ] at ⊢ h_qₑ_div h_rₑ_mod
                  apply congrArg
                  simp [h_qₐ]
                  rw [ProdDropTake.eq.Get.of.GtLength (by omega)]
                  rw [TakeTake.eq.Take.of.Ge (by omega), ← h_qₐrₐ] at h_qₑ_div h_rₑ_mod
                  rw [ProdEraseIdx.eq.MulProdS, Mul_Mul.eq.MulMul] at h_q'_div h_r'_mod
                  rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_q'_div
                  simp at h_r'_mod
                  simp [← h_r_mod] at h_r'_mod
                  simp [h_q'_div] at h_qₑ_div h_rₑ_mod
                  rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₑ_div
                  simp [h_qₑ_div, h_rₑ_mod, h_r'_mod]
                  left
                  rw [Add.comm (a := i.val), Add_Add.eq.AddAdd]
                  simp
                  rw [DivDiv.eq.Div_Mul]
                  rw [Mul.comm (b := (s.take ↑d).prod)]
                  rw [ProdEraseIdx.eq.MulProdS] at h_t
                  simp [Div.eq.Zero.of.Lt h_t]
                  left
                  simp [h_q_div]
                  rw [EqMod.of.Lt]
                  apply LtDiv.of.Lt_Mul h_t
                ·
                  rw [MulProdS.eq.ProdAppend]
                  rw [Rotate.eq.AppendDrop__Take]
              ·
                rw [MulProdS.eq.ProdAppend]
            ·
              rw [MulProdS.eq.ProdAppend]
              simp only [h_toNat]
              simp [Permute__Neg.eq.Append_AppendRotateDropTake]
              left
              simp [ProdRotate.eq.Prod]
        ·
          simp [ProdTake.eq.Mul_ProdTake.of.GtLength d.isLt]
        ·
          have := Gt_0 i
          rwa [ProdTake.eq.DivProdTake.of.Ne_0.GtLength d.isLt (by grind)] at h_q
        ·
          exact i.isLt
      ·
        simp [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength]
        rw [EraseIdx.eq.TailPermute]


-- created on 2025-11-22
-- updated on 2025-11-24
