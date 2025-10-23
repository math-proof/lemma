import Lemma.List.TakeDropPermute.eq.Drop.of.Add.eq.SubLength_1
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.List.ProdDrop.eq.MulProdDrop_Add_1.of.Lt_Length
import Lemma.List.TakeRotate.eq.Drop.of.EqLength_Add
import Lemma.List.TakeDrop.eq.Drop.of.LeLength_Add
import Lemma.List.TailDrop.eq.Drop_Add_1
import Lemma.List.ProdRotate.eq.Prod
import Lemma.Nat.Add_AddMul.lt.Mul_Mul.of.Lt.Lt.Lt
import Lemma.List.DropPermute.eq.RotateTakeDrop.of.Add.eq.SubLength_1
import Lemma.List.DropPermute.eq.ListGet.of.Add.eq.SubLength_1
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.List.RotateRotate.eq.Rotate_Add
import Lemma.List.DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1
import Lemma.List.TakePermute.eq.Take
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.List.TakePermute.eq.TailTake.of.Lt_Length
import Lemma.List.ProdDropTakePermute.eq.Get_0.of.Lt_Length
import Lemma.Nat.EqDivAddMul.of.Lt
import Lemma.List.DropPermute.eq.Drop.of.Lt_Length
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.Nat.LtAddMulAddMul.of.Lt.Lt.Lt.Eq
import Lemma.Nat.LtAdd.of.Lt_Sub
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.Add
import Lemma.Nat.LtVal
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqSub.of.EqAdd
import Lemma.Nat.SubAdd.eq.AddSub.of.Le
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.Nat.EqSubAdd
import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.Permute.eq.Ite
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
open List Tensor Bool Nat Vector
set_option maxHeartbeats 800000


@[main]
private lemma main
  [NeZero (d : ℕ)]
  [NeZero (i : ℕ)]
  {s : List ℕ}
-- given
  (h : i + d = s.length - 1)
  (X : Tensor α s) :
-- imply
  have h_d := NeZero.pos d
  (X.permute ⟨i, by omega⟩ d).permute ⟨i + d, by simp [LengthPermute.eq.Length]; omega⟩ (-d) ≃ X := by
-- proof
  intro h_d
  have h_i_eq : i = s.length - (1 + d) := by omega
  rw [@Tensor.Permute.eq.Ite (i := ⟨i + d, by simp [LengthPermute.eq.Length]; omega⟩) (d := -d)]
  simp
  split_ifs with h_sub h_pos h_j_0 h_eq_d
  repeat omega
  ·
    have h_permute := EqPermutePermute.of.In_Ioo_Length (s := s) (i := i) (j := i + d) ⟨by omega, by omega⟩
    simp at h_permute
    rw [EqSubAdd.left] at h_permute
    have h_i := NeZero.pos i
    have h_lt_add_1 : 1 + d < s.length := by omega
    have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
    apply SEqCast.of.SEq.Eq.Eq
    ·
      rw [h_toNat]
      simp [LengthPermute.eq.Length]
      simp [EqMin.of.Lt h_lt_add_1]
      simp [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (s := (s.permute ⟨i, by grind⟩ d)) (i := ⟨i + d, by grind⟩) (by omega)]
      simp [LengthPermute.eq.Length]
      simp [Add.comm (a := d), EqMin.of.Lt h_lt_add_1]
    ·
      rw [h_permute]
    ·
      rw [h_toNat]
      unfold Tensor.permuteTail
      simp
      apply SEq.of.SEqDataS.Eq
      .
        simp [Add.comm (a := 1)]
        simp [← Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (s := (s.permute ⟨i, by grind⟩ d)) (i := ⟨i + d, by grind⟩) (by omega)]
        simp [h_permute]
      .
        apply SEq.of.All_EqGetS.Eq
        .
          intro t
          have h_t := LtVal t
          simp only [ProdAppend.eq.MulProdS] at h_t
          let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
          have h_q := LtVal q
          have h_r := LtVal r
          simp
          rw [GetCast.eq.Get.of.Eq.Lt]
          .
            rw [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
            unfold Tensor.rotate
            simp
            rw [GetCast.eq.Get.of.Eq.Lt]
            .
              simp [LengthPermute.eq.Length] at h_q
              rw [← h_i_eq, TakePermute.eq.Take ⟨i, by grind⟩] at h_q
              simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_r
              let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r
              have h_qₐ := LtVal qₐ
              have h_rₐ := LtVal rₐ
              simp [LengthPermute.eq.Length, EqMin.of.Lt h_lt_add_1, EqSub_Sub.of.Gt h_lt_add_1, EqMod.of.Lt (show d < 1 + d by omega)] at h_qₐ h_rₐ
              rw [← h_i_eq] at h_qₐ h_rₐ
              simp [DropPermute.eq.ListGet.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h] at h_qₐ
              rw [GetFlatten.eq.Get.of.Eq_AddMul h_qₐrₐ]
              rw [GetTranspose.eq.Get]
              rw [GetSplitAt.eq.Get_AddMul_ProdDrop]
              rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop]
              rw [@Tensor.Permute.eq.Ite (i := ⟨i, by omega⟩) (d := d)]
              simp
              split_ifs with h_sub
              .
                omega
              .
                simp
                have h_lt : q * ((s.permute ⟨i, by grind⟩ d).drop ((s.permute ⟨i, by grind⟩ d).length - (1 + d))).prod + (rₐ * ((s.permute ⟨i, by grind⟩ d).drop ((s.permute ⟨i, by grind⟩ d).length - (1 + d) + (min (1 + d) (s.permute ⟨i, by grind⟩ d).length - 1) % ((s.permute ⟨i, by grind⟩ d).length - ((s.permute ⟨i, by grind⟩ d).length - (1 + d))))).prod + qₐ) < (s.take i).prod * (((s.drop i).take (d + 1)).rotate 1 ++ (s.drop i).drop (d + 1)).prod := by
                  simp [LengthPermute.eq.Length, EqSub_Sub.of.Gt h_lt_add_1]
                  simp [← h_i_eq]
                  simp [EqMin.of.Lt h_lt_add_1, EqMod.of.Lt (show d < 1 + d by omega)]
                  simp [DropPermute.eq.ListGet.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h]
                  rw [Add_Add.eq.AddAdd (a := i)]
                  rw [MulProdS.eq.ProdAppend]
                  rw [AppendRotateTakeDrop.eq.DropPermute (i := ⟨i, by grind⟩)]
                  have h_append := EqAppendTake__Drop ((s.permute ⟨i, by grind⟩ d).drop i) d
                  rw [DropDrop.eq.Drop_Add] at h_append
                  rw [DropPermute.eq.ListGet.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h] at h_append
                  have h_append := congrArg List.prod h_append
                  simp at h_append
                  rw [← h_append]
                  apply Nat.Add_AddMul.lt.Mul_Mul.of.Lt.Lt.Lt
                  .
                    have h_q := LtVal q
                    simp [LengthPermute.eq.Length] at h_q
                    simp [← h_i_eq] at h_q
                    rw [TakePermute.eq.Take (i := ⟨i, by grind⟩)] at h_q
                    exact h_q
                  .
                    exact h_rₐ
                  .
                    exact h_qₐ
                rw [GetCast.eq.Get.of.Eq.Lt]
                .
                  let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
                  let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
                  have h_r' := LtVal r'
                  simp only [ProdAppend.eq.MulProdS] at h_r'
                  rw [GetFlatten.eq.Get.of.Eq_AddMul h_q'r']
                  unfold Tensor.permuteHead
                  simp
                  rw [GetCast.eq.Get.of.Eq.Lt]
                  .
                    unfold Tensor.rotate
                    simp
                    have h_i_add_d_1 : i + (d + 1) = s.length := by omega
                    simp [h_i_add_d_1] at h_r'
                    rw [GetFlatten.eq.Get.of.Eq_AddMul (i := ⟨r', by simp [h_r']⟩) (j := ⟨0, by grind⟩) (by simp [h_i_add_d_1])]
                    rw [GetCast.eq.Get.of.Eq.Lt]
                    .
                      simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_r'
                      let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r'
                      let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                      have h_qₑ := LtVal qₑ
                      have h_rₑ := LtVal rₑ
                      simp [EqMin.of.Le (show d + 1 ≤ s.length - i by omega)] at h_qₑ h_rₑ
                      simp [EqMod.of.Lt (show 1 < d + 1 by omega)] at h_qₑ h_rₑ
                      simp [TakeDrop.eq.Drop.of.LeLength_Add (show i + (d + 1) ≥ s.length by omega)] at h_qₑ h_rₑ
                      rw [GetFlatten.eq.Get.of.Eq_AddMul h_qₑrₑ]
                      rw [GetTranspose.eq.Get]
                      rw [GetSplitAt.eq.Get_AddMul_ProdDrop]
                      repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop]
                      simp [EqMin.of.Le (show d + 1 ≤ s.length - i by omega)]
                      simp [EqMod.of.Lt (show 1 < d + 1 by omega)]
                      simp [h_i_add_d_1]
                      simp [GetElem.getElem]
                      apply congrArg
                      simp [h_qr]
                      simp [LengthPermute.eq.Length, ← h_i_eq]
                      simp [EqMin.of.Lt h_lt_add_1]
                      rw [DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h]
                      simp [RotateRotate.eq.Rotate_Add]
                      rw [ProdRotate.eq.Prod]
                      simp [h_q'_div]
                      simp [LengthPermute.eq.Length]
                      simp [EqSub_Sub.of.Gt h_lt_add_1]
                      simp [EqMin.of.Lt h_lt_add_1, ← h_i_eq]
                      simp [h_i_add_d_1]
                      simp [EqMod.of.Lt (show d < 1 + d by omega)]
                      rw [DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h]
                      simp [ProdRotate.eq.Prod]
                      simp [DropPermute.eq.ListGet.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h]
                      rw [TailTake.eq.TakeTail, TailDrop.eq.Drop_Add_1]
                      rw [TakeDrop.eq.Drop.of.LeLength_Add (show i + 1 + d ≥ s.length by omega)]
                      simp [TakeDrop.eq.Drop.of.LeLength_Add (show i + (d + 1) ≥ s.length by omega)]
                      rw [Nat.DivAddMul.eq.Add_Div.of.Gt_0]
                      .
                        rw [Nat.MulAdd.eq.AddMulS]
                        simp [AddAdd.eq.Add_Add]
                        simp [DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h] at h_rₐ
                        have h_lt := Nat.AddMul.lt.Mul.of.Lt.Lt h_rₐ h_qₐ
                        rw [TakeRotate.eq.Drop.of.EqLength_Add (by grind)] at h_lt
                        simp at h_lt
                        rw [MulProdDrop_Add_1.eq.ProdDrop.of.Lt_Length (by grind)] at h_lt
                        simp [Div.eq.Zero.of.Lt h_lt]
                        simp [EqMin.of.Le (show d + 1 ≤ s.length - i by omega)] at h_qₑ_div h_rₑ_mod
                        simp [EqMod.of.Lt (show 1 < d + 1 by omega)] at h_qₑ_div h_rₑ_mod
                        simp only [TakeDrop.eq.Drop.of.LeLength_Add (show i + (d + 1) ≥ s.length by omega)] at h_qₑ_div h_rₑ_mod
                        simp [TakeDrop.eq.ListGet.of.Lt_Length (show i < s.length by omega)] at h_qₑ_div h_rₑ_mod
                        simp [h_qₑ_div, h_rₑ_mod]
                        have h_r'_mod := h_r'_mod
                        simp [LengthPermute.eq.Length] at h_r'_mod
                        simp [EqMin.of.Lt h_lt_add_1, EqSub_Sub.of.Gt h_lt_add_1, EqMod.of.Lt (show d < 1 + d by omega)] at h_r'_mod
                        rw [← h_i_eq] at h_r'_mod
                        simp [DropPermute.eq.ListGet.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h] at h_r'_mod
                        simp [h_i_add_d_1] at h_r'_mod
                        simp [TakeDrop.eq.Drop.of.LeLength_Add (show i + (d + 1) ≥ s.length by omega)] at h_r'_mod
                        rw [DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h] at h_r'_mod
                        simp [ProdRotate.eq.Prod] at h_r'_mod
                        simp [h_r'_mod]
                        rw [List.TakeRotate.eq.Drop.of.EqLength_Add (by grind)] at h_rₐ
                        simp at h_rₐ
                        simp [EqMod.of.Lt h_lt, EqMod.of.Lt h_qₐ]
                        rw [Nat.DivAddMul.eq.Add_Div.of.Gt_0 (by grind)]
                        simp [Div.eq.Zero.of.Lt h_qₐ]
                        simp [h_qₐrₐ]
                        left
                        simp [LengthPermute.eq.Length, EqMin.of.Lt h_lt_add_1, EqSub_Sub.of.Gt h_lt_add_1, EqMod.of.Lt (show d < 1 + d by omega)]
                        rw [← h_i_eq]
                        rw [TakeDropPermute.eq.Drop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h]
                      .
                        have h_r' := LtVal r'
                        simp [h_i_add_d_1] at h_r'
                        rw [ProdRotate.eq.Prod] at h_r'
                        simp only [List.TakeDrop.eq.Drop.of.LeLength_Add (show i + (d + 1) ≥ s.length by omega)] at h_r'
                        omega
                    .
                      rw [MulProdS.eq.ProdAppend]
                      rwa [AppendDrop__Take.eq.Rotate]
                    .
                      rw [MulProdS.eq.ProdAppend]
                      rw [Rotate.eq.AppendDrop__Take]
                  .
                    exact h_r'
                  .
                    rw [MulProdS.eq.ProdAppend]
                .
                  exact h_lt
                .
                  rw [MulProdS.eq.ProdAppend]
                  rw [Permute.eq.Append_AppendRotateTakeDrop]
            .
              rw [MulProdS.eq.ProdAppend]
              rwa [AppendDrop__Take.eq.Rotate]
            .
              rw [MulProdS.eq.ProdAppend]
              rw [AppendDrop__Take.eq.Rotate]
          .
            assumption
          .
            rw [MulProdS.eq.ProdAppend]
        .
          simp [Add.comm (a := 1)]
          rw [MulProdS.eq.ProdAppend]
          simp [← Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (s := (s.permute ⟨i, by grind⟩ d)) (i := ⟨i + d, by grind⟩) (by omega)]
          simp [h_permute]
  ·
    simp at h_eq_d
    rw [LengthPermute.eq.Length] at h_eq_d
    contradiction


-- created on 2025-10-19
-- updated on 2025-10-22
