import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqPermuteS.of.Le
import Lemma.List.EqPermute__0
import Lemma.List.Permute.eq.Ite
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Nat.Add
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqMin.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Gt_0
import Lemma.Nat.ToNatSub_Neg.eq.Add_1
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqPermuteTail.of.Le_1
import Lemma.Tensor.SEqPermuteTailS.of.LeLength
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open List Tensor Nat Bool Vector Fin
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
  if h_d : i = d then
    subst h_d
    rfl
  else
    have h_d := Gt.of.Ge.Ne h (by omega)
    rw [@Tensor.Permute.eq.Ite]
    simp
    have h_toNat := ToNatSub_Neg.eq.Add1 d
    have h_toNat_i := ToNatSub_Neg.eq.Add_1 i
    split_ifs with h_i0 h_pos? h_i h_length
    repeat omega
    apply SEqCast.of.SEq.Eq
    ·
      rw [h_toNat]
      rw [Permute__Neg.eq.Append_AppendRotateDropTake]
      simp [h_length]
      simp [show (s.length - (1 + d)) = 0 by omega]
      simp [show (s.length - 1 + 1) = s.length by omega]
      simp [show (s.length - 1 - d) = 0 by omega]
      apply congrArg
      omega
    ·
      rw [h_toNat]
      simp [@Tensor.Permute.eq.Ite]
      split_ifs with h_i0 h_pos
      ·
        apply SEq_Cast.of.SEq.Eq
        ·
          simp [h_i0]
          rw [EqPermute__0]
        ·
          have := SEqPermuteTailS.of.LeLength (n := 1 + d) (by omega) X
          apply this.trans
          apply SEqPermuteTail.of.Le_1
          omega
      ·
        omega
      ·
        apply SEq_Cast.of.SEq.Eq
        ·
          rw [h_toNat_i]
          rw [Permute__Neg.eq.Append_AppendRotateDropTake]
          simp [h_length]
          simp [show (s.length - (s.length - 1 + 1)) = 0 by omega]
          simp [show (s.length - 1 + 1) = s.length by omega]
        ·
          rw [h_toNat_i]
          rw [h_length]
          rw [show (s.length - 1 + 1) = s.length by omega]
          apply SEqPermuteTailS.of.LeLength
          omega
    ·
      apply SEq.of.SEqDataS.Eq
      ·
        apply EqPermuteS.of.Le
        omega
      ·
        simp
        apply SEqCast.of.SEq.Eq
        ·
          rw [h_toNat]
          rw [MulProdS.eq.ProdAppend]
          rw [Permute__Neg.eq.Append_AppendRotateDropTake]
          rw [EqMin.of.Ge (by simp; omega)]
          simp [EqMin.of.Le (show i + 1 ≤ s.length by omega)]
          simp [show i + 1 - (1 + d) = i - d by omega]
          left
          left
          rw [EqMin.of.Ge (by omega)]
        ·
          rw [h_toNat]
          apply SEq.of.All_EqGetS.Eq
          ·
            intro t
            have h_t := t.isLt
            let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
            have h_q := q.isLt
            simp only [ProdAppend.eq.MulProdS] at h_q
            let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
            have h_r := r.isLt
            simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
            simp [@Tensor.Permute.eq.Ite]
            split_ifs with h_i0 h_pos
            ·
              unfold Tensor.permuteTail
              simp
              have h_permute : s = (s.permute i (-i)) := by
                simp [h_i0, EqPermute__0]
              simp [DataCast.eq.Cast_Data.of.Eq h_permute]
              simp [h_i0, ProdTake_1.eq.Get_0.of.GtLength_0 (Gt_0 i), ← Prod.eq.Mul_ProdTail.of.GtLength_0] at h_t
              simp [GetElem.getElem]
              repeat rw [GetCast.eq.Get.of.Eq.fin]
              ·
                let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_q
                have h_q' := q'.isLt
                let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
                have h_r' := r'.isLt
                simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_r'
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
                unfold Tensor.rotate
                simp
                rw [GetCast.eq.Get.of.Eq.fin]
                ·
                  let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r'
                  have h_qₐ := qₐ.isLt
                  let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                  have h_rₐ := rₐ.isLt
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
                  simp [EqMod_1'0]
                  simp [h_r'_mod]
                  simp [h_q_div]
                  simp [EqAddMulDiv]
                ·
                  rw [MulProdS.eq.ProdAppend]
                  rw [Rotate.eq.AppendDrop__Take]
              ·
                simp [h_permute]
              ·
                simp
            ·
              omega
            ·
              simp [GetElem.getElem]
              have h_t : t < ((s.take (i + 1)).take ((s.take (i + 1)).length - (1 - -(i : ℤ)).toNat) ++ ((s.take (i + 1)).drop ((s.take (i + 1)).length - (1 - -(i : ℤ)).toNat)).rotate ((1 - -(i : ℤ)).toNat ⊓ (s.take (i + 1)).length - 1)).prod * (s.drop (i + 1)).prod := by
                rw [h_toNat_i]
                rw [show (↑i + 1) ⊓ (s.take (i + 1)).length = i + 1 by simp; omega]
                simp [ProdRotate.eq.Prod]
                simp [ProdRotate.eq.Prod] at h_t
                assumption
              rw [GetCast.eq.Get.of.Eq.fin]
              ·
                let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
                have h_q' := q'.isLt
                simp only [ProdAppend.eq.MulProdS] at h_q'
                let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
                have h_r' := r'.isLt
                have h_r_eq : r.val = r'.val := by grind
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
                unfold Tensor.permuteTail
                simp
                repeat rw [GetCast.eq.Get.of.Eq.fin]
                ·
                  let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_q
                  have h_rₐ := rₐ.isLt
                  let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                  let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_q'
                  have h_rₑ := rₑ.isLt
                  simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_rₐ h_rₑ
                  let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                  repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
                  unfold Tensor.rotate
                  simp
                  repeat rw [GetCast.eq.Get.of.Eq.fin]
                  ·
                    let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul h_rₐ
                    let ⟨qᵢ, rᵢ, h_qᵢrᵢ⟩ := Any_Eq_AddMul.of.Lt_Mul h_rₑ
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
                  ·
                    rw [MulProdS.eq.ProdAppend]
                    rw [Rotate.eq.AppendDrop__Take]
                  ·
                    rw [MulProdS.eq.ProdAppend]
                    rw [Rotate.eq.AppendDrop__Take]
                ·
                  rw [MulProdS.eq.ProdAppend]
                ·
                  rw [MulProdS.eq.ProdAppend]
              ·
                rw [h_toNat_i]
                rw [show (↑i + 1) ⊓ (s.take (i + 1)).length = i + 1 by simp; omega]
                simp [Permute__Neg.eq.Append_AppendRotateDropTake]
          ·
            simp [show (↑i + 1) ⊓ s.length = i + 1 by omega]
            simp [show i + 1 - (1 + d) = i - d by omega]
            simp [show (1 + d) ⊓ (i + 1) = i + 1 by omega]
            simp [show i - d = 0 by omega]
            simp [Permute__Neg.eq.Append_AppendRotateDropTake]


-- created on 2025-10-30
-- updated on 2025-11-03
