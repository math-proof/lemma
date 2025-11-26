import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Int.OfNat.eq.Cast
import Lemma.List.Append_TakeDrop.eq.Take.of.Ge
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.DropAppend.eq.Drop.of.Ge_Length
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length
import Lemma.List.EraseIdxPermute__Neg.eq.EraseIdx.of.Ge
import Lemma.List.EraseIdxRotate.eq.AppendEraseIdxDrop.of.GtLength_Add
import Lemma.List.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
import Lemma.List.GetRotate.eq.Ite.of.GeLength.Lt_Length
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.List.ProdDrop.eq.Get.of.EqLength_Add_1
import Lemma.List.ProdDrop.eq.MulProdS
import Lemma.List.ProdRotate.eq.MulProdS
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTake.eq.MulProdTake.of.Lt_Length
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TailRotate.eq.Take.of.EqLength_Add_1
import Lemma.List.TakeAppend.eq.Take.of.GeLength
import Lemma.List.TakeTake.eq.Take
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.Mul
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Sub_Add.eq.SubSub
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqSumS.of.All_SEq.Eq.Eq
import Lemma.Tensor.Sum.eq.Sum_Select
import Lemma.Tensor.Sum.eq.Sum_Select.of.GtLength
import Lemma.Tensor.SumCast.eq.Cast_Sum.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat Vector List Bool Int Tensor
set_option maxHeartbeats 1000000


@[main]
private lemma main
  [AddCommMonoid α]
  [NeZero (d : ℕ)]
  {i : Fin s.length}
-- given
  (h : i.val + 1 = s.length)
  (h_d : i ≥ d)
  (X : Tensor α s) :
-- imply
  (X.permute i (-d)).sum (i - d) ≃ X.sum i := by
-- proof
  simp [@Tensor.Permute.eq.Ite]
  have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
  rw [Add.comm] at h_toNat
  have := NeZero.pos d
  split_ifs with h_d0 h_pos? h_i0 h_i
  repeat omega
  rw [SumCast.eq.Cast_Sum.of.Eq]
  ·
    apply SEqCast.of.SEq.Eq.Eq
    ·
      rw [h_toNat]
      rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h_i]
    ·
      rw [EraseIdxPermute__Neg.eq.EraseIdx.of.Ge h_d]
    ·
      rw [h_toNat]
      unfold permuteTail Tensor.rotate
      simp
      rw [Sum.eq.Sum_Select]
      rw [Sum.eq.Sum_Select.of.GtLength (by simp; omega)]
      have h_eraseIdx : (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1)).eraseIdx (↑i - d) = s.eraseIdx ↑i := by 
        rw [EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length (by simp; omega)]
        simp
        rw [EraseIdxRotate.eq.AppendEraseIdxDrop.of.GtLength_Add (by simp; omega)]
        conv_rhs => rw [EraseIdx.eq.Append_Drop_Add_1]
        rw [EqMin.of.Le (by omega)]
        simp [h_i]
        rw [@Nat.SubSub.eq.Sub_Add (b := 1)]
        rw [Add.comm (a := 1)]
        simp
        rw [AddAdd.eq.Add_Add]
        rw [EqAddSub.of.Ge (by omega)]
        simp
        rw [EqAddSub.of.Ge (by omega)]
        simp
        have := Append_TakeDrop.eq.Take.of.Ge (s := s) (i := s.length - 1) (d := d) (by omega)
        rw [@Nat.SubSub.eq.Sub_Add (b := 1)] at this
        rwa [Add.comm (a := 1)] at this
      have h_get : (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1))[↑i - d]'(by simp; omega) = s[i] := by 
        rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength (by simp; omega)]
        rw [GetRotate.eq.Ite.of.GeLength.Lt_Length (by simp; omega) (by simp; omega)]
        simp_all
        split_ifs with h_lt
        ·
          simp [EqMin.of.Le (show (d + 1) ≤ s.length by omega)]
          simp only [GetElem.getElem]
          apply congrArg
          simp
          omega
        ·
          omega
      apply SEqSumS.of.All_SEq.Eq.Eq h_eraseIdx h_get
      ·
        intro t
        have h_t := t.isLt
        simp [h_get] at h_t
        have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (s := (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1))) (d := ↑i - d) (i := t) (by simp; omega) (by simp)
        simp at h_length_slice
        apply SEq.of.SEqDataS.Eq h_eraseIdx
        ·
          repeat rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0]
          simp
          apply SEqCastS.of.SEq.Eq.Eq
          ·
            simp [List.Vector.length]
            have := MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (s := (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1))) (d := ↑i - d) (i := t) (by simp; omega) (by simp)
            simp_all
          ·
            simp [List.Vector.length]
            rw [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength]
            simp_all
          ·
            apply SEq.of.All_EqGetS.Eq.fin
            ·
              intro k
              have h_k := k.isLt
              let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_k
              have h_q := q.isLt
              have h_r := r.isLt
              let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
              simp [List.Vector.length] at h_q h_k
              have := LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (s := (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1))) (d := ↑i - d) (i := t) (by simp; omega) (by simp)
              simp at this
              rw [this] at h_q
              rw [h_length_slice, h_eraseIdx] at h_k
              have h_lt : k < (⟨t, (X.data.splitAt (i + 1)).length, s[i.val]⟩ : Slice).length (s.take (i + 1)).prod * (s.drop (↑i + 1)).prod := by 
                simpa [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength _ h_t]
              let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
              have h_q' := q'.isLt
              simp [List.Vector.length] at h_q'
              let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
              have h_prod := ProdTake.eq.MulProdTake.of.Lt_Length (show i < s.length by omega)
              have h_prod' := ProdTake.eq.MulProdTake.of.Lt_Length (show ↑i - d < (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1)).length by simp; omega)
              repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
              repeat rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin _ _ (by simpa [h_get])]
              ·
                repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                rw [GetCast.eq.Get.of.Eq.fin (by simp)]
                simp [h_get]
                simp [EqMin.of.Le (show (d + 1) ≤ s.length by omega)]
                simp [DropAppend.eq.Drop.of.Ge_Length (show (↑i - d + 1) ≥ (s.take (s.length - (d + 1))).length by simp; omega)] at ⊢ h_r h_q_div h_r_mod
                simp [show (↑i - d + 1 - (s.length - (d + 1))) = 1 by simp [h_i]; omega] at ⊢ h_r h_q_div h_r_mod
                have h_sub_min_eq : (d + 1) ⊓ s.length - 1 = d := by omega
                simp [h_sub_min_eq] at h_r h_q_div h_r_mod
                simp [TailRotate.eq.Take.of.EqLength_Add_1 (show (s.drop (s.length - (d + 1))).length = d + 1 by simp; omega)] at ⊢ h_r h_q_div h_r_mod
                have h_sub_eq : s.length - (d + 1) = i - d := by 
                  simp [h_i]
                  omega
                simp [h_sub_eq] at ⊢ h_q h_r h_q_div h_r_mod
                rw [TakeAppend.eq.Take.of.GeLength (show (↑i - d) ≤ (s.take (i - d)).length by simp; omega)] at h_q
                rw [TakeTake.eq.Take] at h_q
                have h_lt : (↑q * s[↑i] + ↑t) * ((s.drop (↑i - d)).take d).prod + ↑r < (s.take (s.length - (d + 1))).prod * ((s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1)).prod := by 
                  simp [h_sub_eq]
                  simp only [ProdRotate.eq.Prod]
                  rw [ProdDrop.eq.MulProdS s (i - d) d]
                  rw [EqAddSub.of.Ge h_d]
                  rw [Mul_Mul.eq.MulMul, MulMul.comm]
                  apply AddMul.lt.Mul.of.Lt.Lt _ h_r
                  rw [ProdDrop.eq.Get.of.EqLength_Add_1 h.symm]
                  apply AddMul.lt.Mul.of.Lt.Lt h_q h_t
                let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
                have h_rₐ := rₐ.isLt
                simp only [ProdRotate.eq.MulProdS] at h_rₐ
                let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
                simp
                rw [GetCast.eq.Get.of.Eq.fin]
                ·
                  let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_rₐ
                  let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₑrₑ]
                  rw [GetTranspose.eq.Get.fin]
                  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                  apply congrArg
                  simp [Drop.eq.Nil.of.Ge_Length (show i + 1 ≥ s.length by simp [h_i]; omega)] at ⊢ h_q'_div h_r'_mod
                  rw [EqMod_1'0] at h_r'_mod
                  simp [h_q'_div, h_r'_mod]
                  simp [h_sub_eq] at ⊢ h_qₑ_div h_rₑ_mod h_qₐ_div h_rₐ_mod
                  have h_q_div := h_q_div
                  simp [h_sub_min_eq] at ⊢ h_qₑ_div h_rₑ_mod h_qₐ_div h_rₐ_mod h_r_mod
                  simp only [ProdRotate.eq.Prod] at h_qₐ_div h_rₐ_mod
                  simp [show s.length - (i - d) = d + 1 by simp [h_i]; omega] at ⊢ h_qₑ_div h_rₑ_mod
                  simp [EqAddSub.of.Ge h_d]
                  simp [h_qₑ_div, h_rₑ_mod]
                  rw [ProdDrop.eq.MulProdS s (i - d) d] at h_qₐ_div h_rₐ_mod
                  rw [EqAddSub.of.Ge h_d] at h_qₐ_div h_rₐ_mod
                  rw [Div_Mul.eq.DivDiv] at h_qₐ_div
                  rw [ProdDrop.eq.Get.of.EqLength_Add_1 h.symm] at *
                  rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₐ_div
                  simp [Div.eq.Zero.of.Lt h_r] at h_qₐ_div
                  rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₐ_div
                  simp [MulAdd.eq.AddMulS, MulMul.comm, AddAdd.eq.Add_Add, MulMul.eq.Mul_Mul, h_r_mod] at h_rₐ_mod
                  rw [EqMod.of.Lt] at h_rₐ_mod
                  ·
                    simp [h_qₐ_div, h_rₐ_mod]
                    simp [Div.eq.Zero.of.Lt h_t]
                    rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)]
                    simp [Add_Add.eq.AddAdd]
                    simp [h_q_div]
                    rw [ProdDrop.eq.MulProdS s (i - d) d]
                    rw [EqAddSub.of.Ge h_d]
                    rw [ProdDrop.eq.Get.of.EqLength_Add_1 h.symm]
                    rw [Mul_Mul.eq.MulMul]
                    simp [AddMulS.eq.MulAdd]
                    left
                    apply EqAddMulDiv
                  ·
                    conv_rhs => rw [Mul.comm]
                    apply AddMul.lt.Mul.of.Lt.Lt h_t
                    apply LtMod.of.Gt_0
                    grind
                ·
                  simp [Rotate.eq.AppendDrop__Take]
              ·
                simp [h_prod]
              ·
                rw [LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength _ h_t] at h_q'
                simp [h_prod]
                rwa [EqDivMul.of.Ne_0 (by simp; omega)]
              ·
                simp [h_prod']
              ·
                simp [h_prod']
                rwa [EqDivMul.of.Ne_0 (by simp; omega)]
            ·
              simp [List.Vector.length]
              rw [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength]
              rw [h_length_slice]
              simp_all
              exact h_t
  ·
    rw [h_toNat]
    rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h_i]
  ·
    omega


-- created on 2025-11-16
-- updated on 2025-11-17
