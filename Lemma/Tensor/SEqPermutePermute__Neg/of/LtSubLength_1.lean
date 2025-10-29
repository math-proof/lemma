import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.DropPermute__Neg.eq.Drop
import Lemma.List.EqPermutePermute__Neg.of.In_Ioo_Length
import Lemma.List.GetTakePermute__Neg.eq.Get
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdDropTake.eq.Get.of.Lt_Length
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTake.eq.Mul_ProdTake.of.Lt_Length
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TailTakePermute__Neg.eq.Take
import Lemma.List.TakePermute__Neg.eq.ListGet
import Lemma.List.TakeTake.eq.Take.of.Gt
import Lemma.Nat.Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtAdd.of.Lt_Sub
import Lemma.Nat.LtVal
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open List Nat Bool Tensor Vector
set_option maxHeartbeats 400000


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {s : List ℕ}
-- given
  (h : d < s.length - 1)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨d, by grind⟩ (-d)).permute ⟨0, by simp; omega⟩ d ≃ X := by
-- proof
  have h_d := NeZero.pos d
  rw [@Tensor.Permute.eq.Ite (i := ⟨0, by simp; omega⟩) (d := d)]
  simp
  split_ifs
  ·
    omega
  ·
    have h_permute := EqPermutePermute__Neg.of.In_Ioo_Length (s := s) (i := d) (j := 0) ⟨by omega, by omega⟩
    simp at h_permute
    have h_lt_add_1 := LtAdd.of.Lt_Sub h
    apply SEqCast.of.SEq.Eq.Eq
    ·
      simp [Permute.eq.Append_AppendRotateTakeDrop]
    ·
      rw [h_permute]
    ·
      unfold Tensor.permuteHead
      simp
      apply SEq.of.SEqDataS.Eq
      ·
        rw [← Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 (by simp; omega), h_permute]
      ·
        simp
        apply SEqCast.of.SEq.Eq.Eq
        ·
          rw [MulProdS.eq.ProdAppend]
        ·
          rw [← Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 (by simp; omega), h_permute]
        ·
          apply SEq.of.All_EqGetS.Eq
          ·
            intro t
            have h_t := LtVal t
            let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
            have h_q := LtVal q
            simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_q
            have h_r := LtVal r
            simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
            unfold Tensor.rotate
            simp only [GetElem.getElem]
            repeat rw [GetCast.eq.Get.of.Eq.Lt.fin]
            ·
              let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q
              have h_q' := LtVal q'
              have h_r' := LtVal r'
              simp at h_q' h_r'
              rw [EqMin.of.Lt h_lt_add_1] at h_q' h_r'
              have h_1_lt : 1 < d + 1 := by omega
              simp [EqMod.of.Lt h_1_lt] at h_q' h_r'
              simp [TailTakePermute__Neg.eq.Take (s := s) (i := ⟨d, by grind⟩)] at h_q'
              rw [TakeTake.eq.Take.of.Gt h_1_lt] at h_r'
              rw [TakePermute__Neg.eq.ListGet] at h_r'
              simp at h_r'
              rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
              rw [GetTranspose.eq.Get.fin]
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              rw [@Tensor.Permute.eq.Ite (i := ⟨d, by omega⟩) (d := -d)]
              simp
              split_ifs
              repeat omega
              simp
              have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
              rw [Add.comm] at h_toNat
              simp [EqMin.of.Lt h_lt_add_1]
              simp [EqMod.of.Lt h_1_lt]
              simp [DropPermute__Neg.eq.Drop (s := s) (i := ⟨d, by grind⟩)]
              simp [TailTakePermute__Neg.eq.Take (s := s) (i := ⟨d, by grind⟩)]
              have h_lt : (r' * (s.take d).prod + q') * (s.drop (d + 1)).prod + r < ((s.take (d + 1)).take ((s.take (d + 1)).length - (1 - -(d : ℤ)).toNat) ++ ((s.take (d + 1)).drop ((s.take (d + 1)).length - (1 - -(d : ℤ)).toNat)).rotate ((1 - -(d : ℤ)).toNat ⊓ (s.take (d + 1)).length - 1)).prod * (s.drop (d + 1)).prod := by
                rw [h_toNat]
                simp [EqMin.of.Lt h_lt_add_1]
                apply AddMul.lt.Mul.of.Lt.Lt
                ·
                  rw [ProdRotate.eq.Prod]
                  rw [ProdTake.eq.Mul_ProdTake.of.Lt_Length]
                  apply AddMul.lt.Mul.of.Lt.Lt h_r' h_q'
                  omega
                ·
                  simp [DropPermute__Neg.eq.Drop (s := s) (i := ⟨d, by grind⟩)] at h_r
                  exact h_r
              rw [GetCast.eq.Get.of.Eq.Lt.fin h_lt]
              ·
                let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
                let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                have h_qₐ := LtVal qₐ
                simp only [ProdAppend.eq.MulProdS] at h_qₐ
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
                unfold Tensor.permuteTail
                simp
                rw [GetCast.eq.Get.of.Eq.Lt.fin h_qₐ]
                ·
                  let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_qₐ
                  let ⟨h_qₑ_div, _⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                  simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₑrₑ]
                  unfold Tensor.rotate
                  simp
                  have h_rₑ := LtVal rₑ
                  simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_rₑ
                  rw [GetCast.eq.Get.of.Eq.Lt.fin h_rₑ]
                  ·
                    let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_rₑ
                    let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
                    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₕrₕ]
                    rw [GetTranspose.eq.Get.fin]
                    repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                    apply congrArg
                    simp only [h_toNat]
                    simp [EqMin.of.Lt h_lt_add_1]
                    simp [ProdDropTake.eq.Get.of.Lt_Length (show d < s.length by omega)]
                    simp [h_qr]
                    simp [DropPermute__Neg.eq.Drop (s := s) (i := ⟨d, by grind⟩)]
                    simp only [h_toNat] at h_qₑ_div
                    simp [EqMin.of.Lt h_lt_add_1, ProdRotate.eq.Prod] at h_qₑ_div
                    simp only [h_toNat] at h_qₐ
                    simp [EqMin.of.Lt h_lt_add_1, ProdRotate.eq.Prod] at h_qₐ
                    simp [Div.eq.Zero.of.Lt h_qₐ] at h_qₑ_div
                    simp [h_qₑ_div] at h_qₑrₑ ⊢
                    simp only [h_toNat] at h_qₕ_div h_rₕ_mod
                    simp [EqMin.of.Lt h_lt_add_1] at h_qₕ_div h_rₕ_mod
                    rw [TakeTake.eq.Take.of.Gt (by omega)] at h_qₕ_div h_rₕ_mod
                    simp [h_qₕ_div, h_rₕ_mod, ← h_qₑrₑ]
                    simp at h_qₐ_div h_rₐ_mod
                    simp [DropPermute__Neg.eq.Drop (s := s) (i := ⟨d, by grind⟩)] at h_r
                    rw [EqMod.of.Lt (by omega)] at h_rₐ_mod
                    simp [h_rₐ_mod]
                    left
                    rw [DivAddMul.eq.Add_Div.of.Gt_0 (by omega)] at h_qₐ_div
                    simp [Div.eq.Zero.of.Lt h_r] at h_qₐ_div
                    simp [h_qₐ_div]
                    rw [DivAddMul.eq.Add_Div.of.Gt_0 (by omega)]
                    simp [Div.eq.Zero.of.Lt h_q', EqMod.of.Lt h_q']
                    simp [h_q'r']
                    left
                    simp [EqMin.of.Lt h_lt_add_1, EqMod.of.Lt h_1_lt]
                    rw [GetTakePermute__Neg.eq.Get]
                    simp
                  ·
                    rw [MulProdS.eq.ProdAppend]
                    rw [Rotate.eq.AppendDrop__Take]
                ·
                  rw [MulProdS.eq.ProdAppend]
              ·
                rw [h_toNat]
                rw [Permute__Neg.eq.Append_AppendRotateTakeDrop]
                simp [EqMin.of.Lt h_lt_add_1]
            ·
              exact h_q
            ·
              rw [MulProdS.eq.ProdAppend]
            ·
              rwa [ProdAppend.eq.MulProdS]
            ·
              rw [Rotate.eq.AppendDrop__Take]
          ·
            rw [MulProdS.eq.ProdAppend]
            rw [← Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 (by simp; omega), h_permute]


-- created on 2025-10-26
-- updated on 2025-10-27
