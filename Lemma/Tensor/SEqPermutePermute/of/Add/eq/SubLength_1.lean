import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.List.DropPermute.eq.AppendRotateTakeDrop
import Lemma.List.DropPermute.eq.ListGet.of.Add.eq.SubLength_1
import Lemma.List.DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1
import Lemma.List.EqAppendTake__Drop
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdDrop.eq.MulProdDrop_Add_1.of.Lt_Length
import Lemma.List.ProdRotate.eq.MulProdS
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.RotateRotate.eq.Rotate_Add
import Lemma.List.TailDrop.eq.Drop_Add_1
import Lemma.List.TakeDrop.eq.Drop.of.LeLength_Add
import Lemma.List.TakeDrop.eq.ListGet.of.Lt_Length
import Lemma.List.TakeDropPermute.eq.Drop.of.Add.eq.SubLength_1
import Lemma.List.TakePermute.eq.Take
import Lemma.List.TakeRotate.eq.Drop.of.EqLength_Add
import Lemma.List.TakeTail.eq.TailTake
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Add_AddMul.lt.Mul_Mul.of.Lt.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqSubAdd
import Lemma.Nat.EqSub_Sub.of.Gt
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtVal
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open List Nat Vector Tensor Bool
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
  (X.permute ⟨i, by omega⟩ d).permute ⟨i + d, by simp; omega⟩ (-d) ≃ X := by
-- proof
  intro h_d
  have h_i_eq : i = s.length - (1 + d) := by omega
  rw [@Tensor.Permute.eq.Ite (i := ⟨i + d, by simp; omega⟩) (d := -d)]
  simp
  split_ifs
  repeat omega
  have h_permute := EqPermutePermute.of.In_Ioo_Length (s := s) (i := i) (j := i + d) ⟨by omega, by omega⟩
  simp at h_permute
  rw [EqSubAdd.left] at h_permute
  have h_i := NeZero.pos i
  have h_Lt1d : 1 + d < s.length := by omega
  have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
  apply SEqCast.of.SEq.Eq.Eq
  ·
    rw [h_toNat]
    simp [EqMin.of.Lt h_Lt1d]
    rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (s := (s.permute ⟨i, by grind⟩ d)) (i := ⟨i + d, by simp; grind⟩) (by simp; omega) d]
    simp [Add.comm (a := d), EqMin.of.Lt h_Lt1d]
  ·
    rw [h_permute]
  ·
    rw [h_toNat]
    unfold Tensor.permuteTail
    simp
    apply SEq.of.SEqDataS.Eq
    ·
      simp [Add.comm (a := 1)]
      have := Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (s := (s.permute ⟨i, by grind⟩ d)) (i := ⟨i + d, by simp; grind⟩) (by simp; omega) d
      simp at this
      rw [← this]
      exact h_permute
    ·
      apply SEq.of.All_EqGetS.Eq
      ·
        intro t
        have h_t := LtVal t
        simp only [ProdAppend.eq.MulProdS] at h_t
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        have h_q := LtVal q
        have h_r := LtVal r
        simp
        rw [GetCast.eq.Get.of.Eq.Lt]
        ·
          rw [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
          unfold Tensor.rotate
          simp
          rw [GetCast.eq.Get.of.Eq.Lt]
          ·
            simp at h_q
            rw [← h_i_eq, TakePermute.eq.Take ⟨i, by grind⟩] at h_q
            simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_r
            let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r
            have h_qₐ := LtVal qₐ
            have h_rₐ := LtVal rₐ
            have h_d_lt_1d : d < 1 + d := by omega
            simp [EqMin.of.Lt h_Lt1d, EqSub_Sub.of.Gt h_Lt1d, EqMod.of.Lt h_d_lt_1d] at h_qₐ h_rₐ
            rw [← h_i_eq] at h_qₐ h_rₐ
            simp [DropPermute.eq.ListGet.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h] at h_qₐ
            rw [GetFlatten.eq.Get.of.Eq_AddMul h_qₐrₐ]
            rw [GetTranspose.eq.Get]
            rw [GetSplitAt.eq.Get_AddMul_ProdDrop]
            rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop]
            rw [@Tensor.Permute.eq.Ite (i := ⟨i, by omega⟩) (d := d)]
            simp
            split_ifs
            ·
              omega
            ·
              simp
              have h_lt : q * ((s.permute ⟨i, by grind⟩ d).drop (s.length - (1 + d))).prod + (rₐ * ((s.permute ⟨i, by grind⟩ d).drop (s.length - (1 + d) + ((1 + d) ⊓ s.length - 1) % (s.length - (s.length - (1 + d))))).prod + qₐ) < (s.take i).prod * (((s.drop i).take (d + 1)).rotate 1 ++ (s.drop i).drop (d + 1)).prod := by
                simp [EqSub_Sub.of.Gt h_Lt1d]
                simp [← h_i_eq]
                simp [EqMin.of.Lt h_Lt1d, EqMod.of.Lt h_d_lt_1d]
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
                apply Add_AddMul.lt.Mul_Mul.of.Lt.Lt.Lt _ h_rₐ h_qₐ
                have h_q := LtVal q
                simp [← h_i_eq] at h_q
                rwa [TakePermute.eq.Take (i := ⟨i, by grind⟩)] at h_q
              rw [GetCast.eq.Get.of.Eq.Lt]
              ·
                let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
                let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
                have h_r' := LtVal r'
                simp only [ProdAppend.eq.MulProdS] at h_r'
                rw [GetFlatten.eq.Get.of.Eq_AddMul h_q'r']
                unfold Tensor.permuteHead
                simp
                rw [GetCast.eq.Get.of.Eq.Lt]
                ·
                  unfold Tensor.rotate
                  simp
                  have h_i_add_d1 : i + (d + 1) = s.length := by omega
                  simp [h_i_add_d1] at h_r'
                  rw [GetFlatten.eq.Get.of.Eq_AddMul (i := ⟨r', by simp [h_r']⟩) (j := ⟨0, by grind⟩) (by simp [h_i_add_d1])]
                  rw [GetCast.eq.Get.of.Eq.Lt]
                  ·
                    simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_r'
                    let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r'
                    let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                    rw [GetFlatten.eq.Get.of.Eq_AddMul h_qₑrₑ]
                    rw [GetTranspose.eq.Get]
                    rw [GetSplitAt.eq.Get_AddMul_ProdDrop]
                    repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop]
                    have h_Led1 : d + 1 ≤ s.length - i := by omega
                    simp [EqMin.of.Le h_Led1]
                    have h_Lt1'd1 : 1 < d + 1 := by omega
                    simp [EqMod.of.Lt h_Lt1'd1]
                    simp [h_i_add_d1]
                    simp [GetElem.getElem]
                    apply congrArg
                    simp [h_qr]
                    simp [← h_i_eq]
                    simp [EqMin.of.Lt h_Lt1d]
                    rw [DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h]
                    simp [RotateRotate.eq.Rotate_Add]
                    rw [ProdRotate.eq.Prod]
                    simp [h_q'_div]
                    simp [EqSub_Sub.of.Gt h_Lt1d]
                    simp [EqMin.of.Lt h_Lt1d, ← h_i_eq]
                    simp [h_i_add_d1]
                    simp [EqMod.of.Lt h_d_lt_1d]
                    rw [DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h]
                    simp [ProdRotate.eq.Prod]
                    simp [DropPermute.eq.ListGet.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h]
                    rw [TailTake.eq.TakeTail, TailDrop.eq.Drop_Add_1]
                    rw [TakeDrop.eq.Drop.of.LeLength_Add (show i + 1 + d ≥ s.length by omega)]
                    have h_Gei_d1 : i + (d + 1) ≥ s.length := by omega
                    simp [TakeDrop.eq.Drop.of.LeLength_Add h_Gei_d1]
                    rw [DivAddMul.eq.Add_Div.of.Gt_0]
                    ·
                      rw [MulAdd.eq.AddMulS]
                      simp [AddAdd.eq.Add_Add]
                      simp [DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h] at h_rₐ
                      have h_lt := AddMul.lt.Mul.of.Lt.Lt h_rₐ h_qₐ
                      rw [TakeRotate.eq.Drop.of.EqLength_Add (by grind)] at h_lt
                      simp at h_lt
                      rw [MulProdDrop_Add_1.eq.ProdDrop.of.Lt_Length (by grind)] at h_lt
                      simp [Div.eq.Zero.of.Lt h_lt]
                      simp [EqMin.of.Le h_Led1] at h_qₑ_div h_rₑ_mod
                      simp [EqMod.of.Lt h_Lt1'd1] at h_qₑ_div h_rₑ_mod
                      simp only [TakeDrop.eq.Drop.of.LeLength_Add h_Gei_d1] at h_qₑ_div h_rₑ_mod
                      simp [TakeDrop.eq.ListGet.of.Lt_Length (show i < s.length by omega)] at h_qₑ_div h_rₑ_mod
                      simp [h_qₑ_div, h_rₑ_mod]
                      simp [EqMin.of.Lt h_Lt1d, EqSub_Sub.of.Gt h_Lt1d, EqMod.of.Lt h_d_lt_1d] at h_r'_mod
                      rw [← h_i_eq] at h_r'_mod
                      simp [DropPermute.eq.ListGet.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h] at h_r'_mod
                      simp [h_i_add_d1] at h_r'_mod
                      simp [TakeDrop.eq.Drop.of.LeLength_Add h_Gei_d1] at h_r'_mod
                      rw [DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h] at h_r'_mod
                      simp [ProdRotate.eq.Prod] at h_r'_mod
                      simp [h_r'_mod]
                      rw [TakeRotate.eq.Drop.of.EqLength_Add (by grind)] at h_rₐ
                      simp at h_rₐ
                      simp [EqMod.of.Lt h_lt, EqMod.of.Lt h_qₐ]
                      rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)]
                      simp [Div.eq.Zero.of.Lt h_qₐ]
                      simp [h_qₐrₐ]
                      left
                      simp [EqMin.of.Lt h_Lt1d, EqSub_Sub.of.Gt h_Lt1d, EqMod.of.Lt h_d_lt_1d]
                      rw [← h_i_eq]
                      rw [TakeDropPermute.eq.Drop.of.Add.eq.SubLength_1 (i := ⟨i, by grind⟩) h]
                    ·
                      have h_r' := LtVal r'
                      simp [h_i_add_d1] at h_r'
                      rw [ProdRotate.eq.Prod] at h_r'
                      simp only [TakeDrop.eq.Drop.of.LeLength_Add h_Gei_d1] at h_r'
                      omega
                  ·
                    rwa [MulProdS.eq.ProdRotate]
                  ·
                    rw [MulProdS.eq.ProdRotate]
                ·
                  exact h_r'
                ·
                  rw [MulProdS.eq.ProdAppend]
              ·
                exact h_lt
              ·
                rw [MulProdS.eq.ProdAppend]
                rw [Permute.eq.Append_AppendRotateTakeDrop]
          ·
            rwa [MulProdS.eq.ProdRotate]
          ·
            rw [MulProdS.eq.ProdRotate]
        ·
          assumption
        ·
          rw [MulProdS.eq.ProdAppend]
      ·
        simp [Add.comm (a := 1)]
        rw [MulProdS.eq.ProdAppend]
        have := Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (s := (s.permute ⟨i, by grind⟩ d)) (i := ⟨i + d, by simp; grind⟩) (by simp; omega) d
        simp at this
        simp [← this]
        rw [h_permute]


-- created on 2025-10-19
-- updated on 2025-10-26
