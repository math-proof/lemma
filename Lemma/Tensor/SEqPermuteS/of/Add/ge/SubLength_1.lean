import Lemma.Nat.Add_1.ge.Mod1
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.ProdTakeDrop.eq.Get.of.Lt_Length
import Lemma.Int.Sub.eq.Zero.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqPermuteS.of.Add.ge.SubLength_1
import Lemma.List.EqPermute__0
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.Permute.eq.Ite
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdPermute.eq.Prod
import Lemma.Nat.EqSub.of.EqAdd
import Lemma.Nat.LtVal
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqPermuteHeadS.of.Ge_Length
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import stdlib.SEq
import sympy.tensor.Basic
open Tensor Bool List Nat Vector Int
set_option maxHeartbeats 400000


@[main]
private lemma main
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i + d ≥ s.length)
  (X : Tensor α s) :
-- imply
  X.permute i d ≃ X.permute i (s.length - i : ℕ) := by
-- proof
  by_cases h_d : i + d = s.length
  ·
    have h_d := Eq_Sub.of.EqAdd.left h_d
    subst h_d
    rfl
  ·
    have h_d := Gt.of.Ge.Ne h h_d
    rw [@Tensor.Permute.eq.Ite]
    simp
    split_ifs with h_d0 h_i? h_i h_length
    ·
      omega
    ·
      have h_s : 0 < s.length := by omega
      have h_i : i = ⟨0, h_s⟩ := by aesop
      subst h_i
      simp_all
      apply SEqCast.of.SEq.Eq
      ·
        simp [Permute.eq.AppendRotateTake___Drop.of.EqVal_0]
      ·
        rw [@Tensor.Permute.eq.Ite]
        simp
        split_ifs with h_s
        ·
          subst h_s
          apply SEq_Cast.of.SEq.Eq
          ·
            simp
            rw [EqPermute__0]
          ·
            simp at h_s
        ·
          apply SEq_Cast.of.SEq.Eq
          ·
            simp [Permute.eq.AppendRotateTake___Drop.of.EqVal_0]
          ·
            have := SEqPermuteHeadS.of.Ge_Length (s := s) (n := d + 1) (by omega) X
            apply SEq.trans this
            have := SEqPermuteHeadS.of.Ge_Length (s := s) (n := s.length + 1) (by omega) X
            apply SEq.symm ∘ SEq.trans this
            rfl
    ·
      apply SEq.of.SEqDataS.Eq
      ·
        rw [EqPermuteS.of.Add.ge.SubLength_1 (s := s) (i := i) (d := d) (by omega)]
        rw [EqPermuteS.of.Add.ge.SubLength_1 (s := s) (i := i) (d := s.length - i) (by omega)]
      ·
        simp
        apply SEqCast.of.SEq.Eq
        ·
          rw [MulProdS.eq.ProdAppend]
          apply congrArg
          rw [Permute.eq.Append_AppendRotateTakeDrop]
        ·
          rw [@Tensor.Permute.eq.Ite]
          simp
          split_ifs with h_s
          ·
            omega
          ·
            simp
            apply SEq_Cast.of.SEq.Eq
            ·
              rw [MulProdS.eq.ProdAppend]
              rw [Permute.eq.Append_AppendRotateTakeDrop]
            ·
              apply SEq.of.All_EqGetS.Eq
              .
                intro t
                have h_t := LtVal t
                let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
                let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
                have h_r := Nat.LtVal r
                simp only [ProdAppend.eq.MulProdS] at h_r
                simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
                unfold Tensor.permuteHead
                simp
                have h_take : (s.drop ↑i).take (d + 1) = (s.drop ↑i).take (s.length - ↑i + 1) := by
                  repeat rw [EqTake.of.Ge_Length]
                  repeat simp
                  omega
                have h_drop : (s.drop ↑i).drop (d + 1) = (s.drop ↑i).drop (s.length - ↑i + 1) := by
                  simp
                  repeat rw [Drop.eq.Nil.of.Ge_Length]
                  simp
                  repeat omega
                simp only [h_take, h_drop] at h_t
                let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
                let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
                simp [Drop.eq.Nil.of.Ge_Length (show i + (d + 1) ≥ s.length by omega)] at h_q_div h_r_mod
                simp [Drop.eq.Nil.of.Ge_Length (show (↑i + (s.length - ↑i + 1)) ≥ s.length by omega)] at h_q'_div h_r'_mod
                simp [EqTake.of.Ge_Length (show d + 1 ≥ (s.drop ↑i).length by simp; omega)] at h_q_div h_r_mod
                simp [EqTake.of.Ge_Length (show (s.length - ↑i + 1) ≥ (s.drop ↑i).length by simp)] at h_q'_div h_r'_mod
                have h_q_eq : q = q' := by grind
                have h_r_eq : r.val = r'.val := by grind
                have h_r' := Nat.LtVal r'
                simp only [ProdAppend.eq.MulProdS] at h_r'
                simp [GetFlatten.eq.Get.of.Eq_AddMul h_q'r']
                repeat rw [GetCast.eq.Get.of.Eq.Lt]
                .
                  let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r
                  let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                  have h_qₐ := Nat.LtVal qₐ
                  have h_rₐ := Nat.LtVal rₐ
                  simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₐ
                  simp [Drop.eq.Nil.of.Ge_Length (show i + (d + 1) ≥ s.length by omega)] at h_rₐ h_qₐ_div
                  let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r'
                  let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
                  have h_qₑ := Nat.LtVal qₑ
                  have h_rₑ := Nat.LtVal rₑ
                  simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_qₑ
                  simp [Drop.eq.Nil.of.Ge_Length (show ↑i + (s.length - ↑i + 1) ≥ s.length by omega)] at h_rₑ h_qₑ_div
                  have h_qₐₑ_eq : qₐ.val = qₑ.val := by grind
                  simp [GetFlatten.eq.Get.of.Eq_AddMul h_qₐrₐ]
                  simp [GetFlatten.eq.Get.of.Eq_AddMul h_qₑrₑ]
                  unfold Tensor.rotate
                  simp [GetElem.getElem]
                  repeat rw [GetCast.eq.Get.of.Eq.Lt.fin]
                  .
                    let ⟨qₕ, rₕ, h_qₕrₕ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_qₐ
                    let ⟨h_qₕ_div, h_rₕ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₕrₕ
                    let ⟨qᵢ, rᵢ, h_qᵢrᵢ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_qₑ
                    let ⟨h_qᵢ_div, h_rᵢ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qᵢrᵢ
                    simp [EqMin.of.Ge (show d + 1 ≥ s.length - i by simp; omega)] at h_qₕ_div h_rₕ_mod
                    have := Nat.Add_1.ge.Mod1 (s.length - ↑i)
                    simp [TakeTake.eq.Take.of.Ge this] at h_qᵢ_div h_rᵢ_mod
                    have := Nat.Add_1.ge.Mod1 d (s.length - ↑i)
                    rw [TakeTake.eq.Take.of.Ge this] at h_qₕ_div h_rₕ_mod
                    have h_qₕᵢ_eq : qₕ.val = qᵢ.val := by grind
                    have h_rₕᵢ_eq : rₕ.val = rᵢ.val := by grind
                    repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
                    repeat rw [GetTranspose.eq.Get.fin]
                    repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                    apply congrArg
                    simp [h_q_eq, h_rₐ, h_rₑ]
                    rw [EqMin.of.Ge (by omega)]
                    simp [TakeDrop.eq.DropTake]
                    simp [EqTake.of.Ge_Length (show (↑i + (d + 1)) ≥ s.length by omega)]
                    simp [Drop.eq.Nil.of.Ge_Length (show i + (d + 1) ≥ s.length by simp; omega)]
                    simp [EqTake.of.Ge_Length (show (↑i + (s.length - ↑i + 1)) ≥ s.length by omega)]
                    simp [Drop.eq.Nil.of.Ge_Length (show (↑i + (s.length - ↑i + 1)) ≥ s.length by simp; omega)]
                    simp [h_qₕᵢ_eq, h_rₕᵢ_eq]
                  .
                    exact h_qₑ
                  .
                    rw [MulProdS.eq.ProdAppend]
                    rw [List.Rotate.eq.AppendDrop__Take]
                  .
                    exact h_qₐ
                  .
                    rw [MulProdS.eq.ProdAppend]
                    rw [List.Rotate.eq.AppendDrop__Take]
                .
                  exact h_r'
                .
                  rw [MulProdS.eq.ProdAppend]
                .
                  exact h_r
                .
                  rw [MulProdS.eq.ProdAppend]
              .
                repeat rw [MulProdS.eq.ProdAppend]
                repeat rw [← Permute.eq.Append_AppendRotateTakeDrop]
                repeat rw [ProdPermute.eq.Prod]
    ·
      omega
    ·
      omega


-- created on 2025-10-29
-- updated on 2025-10-30
