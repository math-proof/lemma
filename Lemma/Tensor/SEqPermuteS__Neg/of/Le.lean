import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.Prod.eq.MulProdS
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.SEqPermuteTail.of.Le_1
import Lemma.Tensor.SEqPermuteTailS.of.Ge_Length
import Lemma.Tensor.SEqPermuteTailS.of.SEq.Eq
import Lemma.List.EqPermuteS.of.Le
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.EqPermuteS.of.Add.ge.SubLength_1
import Lemma.List.EqPermute__0
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute.eq.Ite
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdPermute.eq.Prod
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.Add_1.ge.Mod1
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Eq.of.Sub.eq.Zero.Ge
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqMin.of.Ge
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.EqSub.of.EqAdd
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtVal
import Lemma.Nat.SubSub
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqPermuteHeadS.of.Ge_Length
import Lemma.Tensor.SEqPermuteHead_1
import Lemma.Tensor.SEqPermuteTail_1
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat Tensor Bool List Vector
set_option maxHeartbeats 800000


@[main]
private lemma main
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i ≤ d)
  (X : Tensor α s) :
-- imply
  X.permute i (-d) ≃ X.permute i (-i) := by
-- proof
  by_cases h_d : i = d
  .
    subst h_d
    rfl
  .
    have h_d := Gt.of.Ge.Ne h (by omega)
    rw [@Tensor.Permute.eq.Ite]
    simp
    have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
    have h_toNat_i := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 i
    rw [Add.comm] at h_toNat_i
    split_ifs with h_i0 h_pos? h_i h_length
    repeat omega
    apply SEqCast.of.SEq.Eq
    .
      rw [h_toNat]
      rw [List.Permute__Neg.eq.Append_AppendRotateTakeDrop]
      simp [h_length]
      simp [show (s.length - (1 + d)) = 0 by omega]
      simp [show (s.length - 1 + 1) = s.length by omega]
      simp [show (s.length - 1 - d) = 0 by omega]
      apply congrArg
      omega
    .
      rw [h_toNat]
      simp [@Tensor.Permute.eq.Ite]
      split_ifs with h_i0 h_pos
      .
        apply SEq_Cast.of.SEq.Eq
        .
          simp [h_i0]
          rw [List.EqPermute__0]
        .
          have := Tensor.SEqPermuteTailS.of.Ge_Length (n := 1 + d) (by omega) X
          apply SEq.trans this
          apply Tensor.SEqPermuteTail.of.Le_1
          omega
      .
        omega
      .
        apply SEq_Cast.of.SEq.Eq
        .
          rw [h_toNat_i]
          rw [List.Permute__Neg.eq.Append_AppendRotateTakeDrop]
          simp [h_length]
          simp [show (s.length - (s.length - 1 + 1)) = 0 by omega]
          simp [show (s.length - 1 + 1) = s.length by omega]
        .
          rw [h_toNat_i]
          rw [h_length]
          rw [show (s.length - 1 + 1) = s.length by omega]
          apply Tensor.SEqPermuteTailS.of.Ge_Length
          omega
    .
      apply SEq.of.SEqDataS.Eq
      .
        apply List.EqPermuteS.of.Le
        omega
      .
        simp
        apply SEqCast.of.SEq.Eq
        .
          rw [h_toNat]
          rw [MulProdS.eq.ProdAppend]
          rw [List.Permute__Neg.eq.Append_AppendRotateTakeDrop]
          rw [EqMin.of.Ge (by simp; omega)]
          simp [EqMin.of.Le (show i + 1 ≤ s.length by omega)]
          simp [show i + 1 - (1 + d) = i - d by omega]
          left
          left
          rw [EqMin.of.Ge (by omega)]
        .
          rw [h_toNat]
          apply SEq.of.All_EqGetS.Eq
          .
            intro t
            have h_t := LtVal t
            let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
            have h_q := LtVal q
            simp only [ProdAppend.eq.MulProdS] at h_q
            let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
            have h_r := LtVal r
            simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
            simp [@Tensor.Permute.eq.Ite]
            split_ifs with h_i0 h_pos
            .
              unfold Tensor.permuteTail
              simp
              have h_permute: s = (s.permute i (-i)) := by
                simp [h_i0, List.EqPermute__0]
              simp [DataCast.eq.Cast_Data.of.Eq h_permute]
              simp [h_i0, List.ProdTake_1.eq.Get_0.of.GtLength_0 (Gt_0 i), ← List.Prod.eq.Mul_ProdTail.of.GtLength_0] at h_t
              simp [GetElem.getElem]
              repeat rw [GetCast.eq.Get.of.Eq.fin]
              .
                let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q
                have h_q' := LtVal q'
                let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
                have h_r' := LtVal r'
                simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_r'
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
                unfold Tensor.rotate
                simp
                rw [GetCast.eq.Get.of.Eq.fin]
                .
                  let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r'
                  have h_qₐ := LtVal qₐ
                  let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                  have h_rₐ := LtVal rₐ
                  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
                  rw [GetTranspose.eq.Get.fin]
                  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                  apply congrArg
                  simp [h_i0]
                  simp [h_i0] at h_qr h_q'_div h_qₐ_div h_rₐ_mod h_r'_mod h_q_div
                  simp [h_qr]
                  left
                  simp [h_q'_div]
                  simp [h_qₐ_div, h_rₐ_mod]
                  simp [Nat.EqMod_1'0]
                  simp [h_r'_mod]
                  simp [h_q_div]
                  simp [← Nat.Eq_AddMulDiv___Mod]
                .
                  rw [MulProdS.eq.ProdAppend]
                  rw [Rotate.eq.AppendDrop__Take]
              .
                simp [h_permute]
              .
                simp
            .
              omega
            .
              simp [GetElem.getElem]
              have h_t : t < ((s.take (i + 1)).take ((s.take (i + 1)).length - (1 - -(i : ℤ)).toNat) ++ ((s.take (i + 1)).drop ((s.take (i + 1)).length - (1 - -(i : ℤ)).toNat)).rotate ((1 - -(i : ℤ)).toNat ⊓ (s.take (i + 1)).length - 1)).prod * (s.drop (i + 1)).prod := by
                rw [h_toNat_i]
                rw [show (↑i + 1) ⊓ (s.take (i + 1)).length = i + 1 by simp; omega]
                simp [ProdRotate.eq.Prod]
                simp [ProdRotate.eq.Prod] at h_t
                assumption
              rw [GetCast.eq.Get.of.Eq.fin]
              .
                let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
                have h_q' := LtVal q'
                simp only [ProdAppend.eq.MulProdS] at h_q'
                let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
                have h_r' := LtVal r'
                have h_r_eq : r.val = r'.val := by grind
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
                unfold Tensor.permuteTail
                simp
                repeat rw [GetCast.eq.Get.of.Eq.fin]
                .
                  let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q
                  have h_rₐ := LtVal rₐ
                  let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                  let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q'
                  have h_rₑ := LtVal rₑ
                  simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_rₐ h_rₑ
                  let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                  repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
                  unfold Tensor.rotate
                  simp
                  repeat rw [GetCast.eq.Get.of.Eq.fin]
                  .
                    let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_rₐ
                    let ⟨qᵢ, rᵢ, h_qᵢrᵢ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_rₑ
                    let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
                    let ⟨h_qᵢ_div, h_rᵢ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qᵢrᵢ
                    repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
                    repeat rw [GetTranspose.eq.Get.fin]
                    repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                    apply congrArg
                    simp only [h_toNat_i] at h_qₑ_div h_rₐ_mod h_rₑ_mod h_qᵢ_div h_rᵢ_mod ⊢
                    simp [ProdRotate.eq.Prod] at h_qₐ_div h_qₑ_div h_rₐ_mod h_rₑ_mod
                    simp [show (↑i + 1) ⊓ s.length = i + 1 by omega] at h_qₐ_div h_rₐ_mod h_rₑ_mod h_qₕ_div h_qᵢ_div h_rₕ_mod h_rᵢ_mod ⊢
                    simp [show i + 1 - (1 + d) = i - d by omega] at h_qₐ_div h_rₐ_mod h_qₕ_div h_rₕ_mod ⊢
                    simp [show i - d = 0 by omega] at h_qₐ_div h_rₐ_mod h_qₕ_div h_rₕ_mod ⊢
                    simp [show (1 + d) ⊓ (i + 1) = i + 1 by omega] at h_qₕ_div h_rₕ_mod ⊢
                    have h_qₐₑ_eq : qₐ.val = qₑ.val := by grind
                    have h_rₐₑ_eq : rₐ.val = rₑ.val := by grind
                    have h_qₕᵢ_eq : qₕ.val = qᵢ.val := by grind
                    have h_rₕᵢ_eq : rₕ.val = rᵢ.val := by grind
                    simp [h_qₐₑ_eq, h_r_eq, h_rₕᵢ_eq, h_qₕᵢ_eq]
                  .
                    rw [MulProdS.eq.ProdAppend]
                    rw [Rotate.eq.AppendDrop__Take]
                  .
                    rw [MulProdS.eq.ProdAppend]
                    rw [Rotate.eq.AppendDrop__Take]
                .
                  rw [MulProdS.eq.ProdAppend]
                .
                  rw [MulProdS.eq.ProdAppend]
              .
                rw [h_toNat_i]
                rw [show (↑i + 1) ⊓ (s.take (i + 1)).length = i + 1 by simp; omega]
                simp [List.Permute__Neg.eq.Append_AppendRotateTakeDrop]
          .
            simp [show (↑i + 1) ⊓ s.length = i + 1 by omega]
            simp [show i + 1 - (1 + d) = i - d by omega]
            simp [show (1 + d) ⊓ (i + 1) = i + 1 by omega]
            simp [show i - d = 0 by omega]
            simp [List.Permute__Neg.eq.Append_AppendRotateTakeDrop]


-- created on 2025-10-30
