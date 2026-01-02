import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Int.OfNat.eq.Cast
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.DropPermute__Neg.eq.AppendDropTake.of.Ge.GtLength
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.EraseIdxPermute__Neg.eq.EraseIdx.of.Ge
import Lemma.List.Get.dvd.ProdTake.of.GtLength
import Lemma.List.GetPermute__Neg.eq.Get.of.Ge
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.List.ProdRotate.eq.MulProdS
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.List.ProdTake.eq.Mul_ProdTake.of.GtLength
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakePermute__Neg.eq.Take
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.Add
import Lemma.Nat.Add.ge.Sub
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.DivDiv
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqSubAdd
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LeAddS.is.Le
import Lemma.Nat.LeAdd_1
import Lemma.Nat.LtDiv.of.Lt_Mul
import Lemma.Nat.LtSub.of.Lt
import Lemma.Nat.Lt_Sub_Sub.of.Ge.Gt
import Lemma.Nat.ModDivMod_Mul.eq.ModDiv
import Lemma.Nat.Mul
import Lemma.Nat.Lt0Mul.of.Gt_0.Gt_0
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Ne_0.of.Gt
import Lemma.Nat.SubAddS.eq.Sub
import Lemma.Nat.Sub_Sub.eq.Add.of.Ge
import Lemma.Nat.ToNatSub_Neg.eq.Add_1
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqSumS.of.All_SEq.Eq.Eq
import Lemma.Tensor.Sum.eq.Sum_Select
import Lemma.Tensor.Sum.eq.Sum_Select.of.GtLength
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Int Nat Tensor List Bool Vector Fin
set_option maxHeartbeats 1000000


@[main]
private lemma main
  [AddCommMonoid α]
  [NeZero (d : ℕ)]
  {i : Fin s.length}
-- given
  (h_i : i.val + 1 < s.length)
  (h_d : i ≥ d)
  (X : Tensor α s) :
-- imply
  (X.permute i (-d)).sum (i - d) ≃ X.sum i := by
-- proof
  simp [@Tensor.Permute.eq.Ite]
  have h_toNat := ToNatSub_Neg.eq.Add_1 d
  have h_sub_lt : (s.permute i (-d)).length > i - d := by
    simp
    apply LtSub.of.Lt i.isLt
  have := NeZero.pos d
  split_ifs
  repeat omega
  rw [Sum.eq.Sum_Select]
  rw [Sum.eq.Sum_Select.of.GtLength]
  have h_eraseIdx := EraseIdxPermute__Neg.eq.EraseIdx.of.Ge h_d
  have h_get := GetPermute__Neg.eq.Get.of.Ge (d := d) h_d
  apply SEqSumS.of.All_SEq.Eq.Eq h_eraseIdx h_get
  ·
    intro t
    have h_t := t.isLt
    apply SEq.of.SEqDataS.Eq h_eraseIdx
    simp
    repeat rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData]
    simp
    simp [h_get] at h_t
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp
      rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
      simpa [h_get]
    ·
      simp
      rw [LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength (by omega) (by omega)]
      rw [ProdEraseIdx.eq.MulProdS]
    ·
      simp at h_get
      apply SEq.of.All_EqGetS.Eq.fin
      ·
        have h_ne_0 := Ne_0.of.Gt h_t
        intro k
        have h_k := k.isLt
        obtain ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_k
        have h_r := r.isLt
        obtain ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        have h_drop_permute := DropPermute__Neg.eq.AppendDropTake.of.Ge.GtLength i.isLt h_d
        simp [h_drop_permute] at h_r h_q_div h_r_mod
        have h_q := q.isLt
        simp at h_k
        rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength h_sub_lt (by simpa [h_get])] at h_k
        rw [EraseIdxPermute__Neg.eq.EraseIdx.of.Ge h_d] at h_k
        have h_lt : k < (⟨t, (X.data.splitAt (i + 1)).length, s[i]⟩ : Slice).length (s.take (i + 1)).prod * (s.drop (i + 1)).prod := by
          simp
          rwa [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength (by simp) (by omega)]
        obtain ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
        obtain ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        have h_q' := q'.isLt
        simp [List.Vector.length] at h_q
        rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength h_sub_lt (by simpa [h_get])] at h_q
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
        rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd _ _ (by simpa [h_get])]
        simp [List.Vector.length]
        have h_i1_le := LeAdd_1 i
        have h_LeAddS := LeAddS.of.Le 1 h_d
        rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin _ _ h_t]
        ·
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          rw [GetCast.eq.Get.of.Eq.fin]
          ·
            simp [h_drop_permute, h_get]
            have h_lt : (↑q * s[i.val] + ↑t) * (((s.take ↑i).drop (↑i - d)).prod * (s.drop (↑i + 1)).prod) + ↑r < ((s.take (↑i + 1)).take ((s.take (↑i + 1)).length - (1 - -(d : ℤ)).toNat) ++ ((s.take (↑i + 1)).drop ((s.take (↑i + 1)).length - (1 - -(d : ℤ)).toNat)).rotate ((1 - -(d : ℤ)).toNat ⊓ (s.take (↑i + 1)).length - 1)).prod * (s.drop (↑i + 1)).prod := by
              simp only [h_toNat]
              simp
              rw [EqMin.of.Le h_i1_le]
              rw [SubAddS.eq.Sub]
              rw [EqMin.of.Le h_LeAddS]
              rw [@Nat.EqSubAdd]
              rw [ProdRotate.eq.Prod]
              rw [MulMul.eq.Mul_Mul]
              conv_rhs => simp [DropTake.eq.TakeDrop]
              rw [Sub_Sub.eq.Add.of.Ge.comm]
              have := Lt_Sub_Sub.of.Ge.Gt i.isLt h_d
              rw [ProdTake.eq.Mul_ProdTake.of.GtLength (show d < (s.drop (i - d)).length by simpa)]
              simp [TakeDrop.eq.DropTake]
              simp [EqAddSub.of.Ge h_d]
              repeat conv_rhs => rw [Mul_Mul.eq.MulMul]
              rw [MulMul.eq.Mul_Mul]
              apply AddMul.lt.Mul.of.Lt.Lt
              ·
                apply AddMul.lt.Mul.of.Lt.Lt _ h_t
                ·
                  exact h_sub_lt
                ·
                  rw [TakePermute__Neg.eq.Take] at h_q
                  rwa [TakeTake.eq.Take.of.Ge (Add.ge.Sub i 1 d)]
              ·
                exact h_r
              ·
                exact h_d
            let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
            let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
            have h_qₐ := qₐ.isLt
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
            unfold permuteTail Tensor.rotate
            simp
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              simp only [ProdAppend.eq.MulProdS] at h_qₐ
              let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_qₐ
              let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
              have h_rₑ := rₑ.isLt
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₑrₑ]
              simp
              rw [GetCast.eq.Get.of.Eq.fin]
              ·
                simp only [ProdRotate.eq.MulProdS] at h_rₑ
                let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul h_rₑ
                let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₕrₕ]
                rw [GetTranspose.eq.Get.fin]
                repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                apply congrArg
                simp only [h_toNat] at *
                simp at ⊢ h_qₕ_div h_rₕ_mod h_qₑ_div h_rₑ_mod
                rw [EqMin.of.Le h_i1_le] at ⊢ h_qₕ_div h_rₕ_mod h_qₑ_div h_rₑ_mod
                rw [SubAddS.eq.Sub] at ⊢ h_qₕ_div h_rₕ_mod h_qₑ_div h_rₑ_mod
                rw [EqMin.of.Le h_LeAddS] at ⊢ h_qₕ_div h_rₕ_mod h_qₑ_div h_rₑ_mod
                rw [@Nat.EqSubAdd] at *
                simp [DropTake.eq.TakeDrop] at ⊢ h_qₕ_div h_rₕ_mod h_qₑ_div h_rₑ_mod
                rw [Sub_Sub.eq.Add.of.Ge.comm (by omega)] at *
                rw [EqMod.of.Lt (show d < (d + 1) by omega)] at *
                rw [TakeTake.eq.Take.of.Ge (by omega)] at h_qₕ_div h_rₕ_mod
                simp [TakeDrop.eq.DropTake] at h_qₕ_div h_rₕ_mod
                rw [EqAddSub.of.Ge h_d] at *
                rw [@Nat.EqSubAdd.left]
                rw [ProdTake_1.eq.Get_0.of.GtLength_0 (by simp)]
                simp
                simp [Mul_Mul.eq.MulMul] at h_rₐ_mod
                simp [ProdRotate.eq.Prod] at *
                rw [ProdTake.eq.Mul_ProdTake.of.GtLength (by simp; omega)] at ⊢ h_qₑ_div h_rₑ_mod
                simp at ⊢ h_qₑ_div h_rₑ_mod
                simp [TakeDrop.eq.DropTake] at ⊢ h_qₑ_div h_rₑ_mod
                simp [EqAddSub.of.Ge h_d] at ⊢ h_qₑ_div h_rₑ_mod
                simp [h_rₑ_mod] at h_qₕ_div h_rₕ_mod
                rw [Mul_Mul.eq.MulMul] at h_qₐ_div
                rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₐ_div
                simp [h_qₐ_div] at h_qₕ_div h_rₕ_mod
                rw [MulAdd.eq.AddMulS] at h_qₕ_div
                simp [MulMul.eq.Mul_Mul, AddAdd.eq.Add_Add] at h_qₕ_div
                rw [EqMod.of.Lt (AddMul.lt.Mul.of.Lt.Lt h_t (LtDiv.of.Lt_Mul h_r))] at h_qₕ_div
                rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₕ_div
                rw [h_qₕ_div]
                repeat rw [MulAdd.eq.AddMulS]
                repeat rw [Add_Add.eq.AddAdd, AddAdd.comm]
                conv_rhs => rw [AddAdd.comm]
                simp [h_r'_mod, h_r_mod, h_rₐ_mod]
                rw [DivDiv.comm]
                simp [DivDiv.eq.Div_Mul]
                rw [Mul.comm (a := s[i.val])]
                rw [Mul_Mul.eq.MulMul]
                rw [MulMul.eq.Mul_Mul]
                conv_lhs =>
                  arg 2
                  rw [MulMul.eq.Mul_Mul]
                conv_rhs =>
                  rw [MulMul.eq.Mul_Mul]
                simp [AddMulS.eq.MulAdd]
                left
                rw [MulAdd.eq.AddMulS, MulMul.eq.Mul_Mul, AddAdd.eq.Add_Add] at h_qₐ_div
                simp [h_rₕ_mod, h_qₑ_div, h_r_mod, h_qₐ_div]
                rw [DivAddMul.eq.Add_Div.of.Gt_0]
                ·
                  rw [Div_Mul.eq.DivDiv.comm]
                  rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)]
                  simp [DivDiv.eq.Div_Mul.comm, Div.eq.Zero.of.Lt h_t, h_q_div]
                  rw [Div_Mul.eq.DivDiv.comm]
                  rw [ModDivMod_Mul.eq.ModDiv]
                  simp [← h_q'_div]
                  apply EqAddMulDiv
                ·
                  apply Lt0Mul.of.Gt_0.Gt_0
                  repeat grind
              ·
                rw [MulProdS.eq.ProdAppend]
                rw [Rotate.eq.AppendDrop__Take]
            ·
              rw [MulProdS.eq.ProdAppend]
          ·
            rw [h_toNat]
            rw [MulProdS.eq.ProdAppend]
            apply congrArg
            simp
            rw [EqMin.of.Le h_i1_le]
            rw [SubAddS.eq.Sub]
            rw [EqMin.of.Le h_LeAddS]
            rw [@Nat.EqSubAdd]
            rw [Permute__Neg.eq.Append_AppendRotateDropTake]
            rw [EqMin.of.Le (by omega)]
            rw [Append_Append.eq.AppendAppend]
        ·
          apply Get.dvd.ProdTake.of.GtLength
        ·
          simp [List.Vector.length] at h_q'
          rw [LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength (by simp) (by simpa [h_get])] at h_q'
          simp [ProdTake.eq.MulProdTake.of.GtLength i.isLt]
          rwa [EqDivMul.of.Ne_0 h_ne_0]
        ·
          apply Get.dvd.ProdTake.of.GtLength
        ·
          simp [ProdTake.eq.MulProdTake.of.GtLength h_sub_lt]
          rwa [EqDivMul.of.Ne_0]
          rwa [h_get]
      ·
        simp
        rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
        ·
          rw [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength _ h_t]
          rw [h_eraseIdx]
        ·
          simpa [h_get]


-- created on 2025-11-16
