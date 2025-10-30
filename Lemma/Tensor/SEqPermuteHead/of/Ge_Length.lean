import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqMin.of.Ge
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.LtVal
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Nat Bool List Tensor Vector


@[main]
private lemma main
-- given
  (h : n ≥ s.length)
  (X : Tensor α s) :
-- imply
  X.permuteHead n ≃ X.permuteHead s.length := by
-- proof
  unfold Tensor.permuteHead
  simp
  apply SEq.of.SEqDataS.Eq
  ·
    simp
    rw [EqTake.of.Ge_Length h]
    rw [Drop.eq.Nil.of.Ge_Length h]
    simp
  ·
    simp
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      rw [MulProdS.eq.ProdAppend]
    ·
      rw [MulProdS.eq.ProdAppend]
    ·
      apply SEq.of.All_EqGetS.Eq
      ·
        intro t
        have h_t := LtVal t
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        let ⟨h_q_div, _⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        have h_q := LtVal q
        have h_r := LtVal r
        simp [Drop.eq.Nil.of.Ge_Length h] at h_r
        simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
        simp [Drop.eq.Nil.of.Ge_Length h] at h_t
        simp [EqTake.of.Ge_Length h] at h_t
        have h_t : t < ((s.take s.length).rotate 1).prod * (s.drop s.length).prod := by simpa
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        let ⟨h_q'_div, _⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        simp at h_q_div h_q'_div
        simp [Drop.eq.Nil.of.Ge_Length h] at h_q_div
        have h_eq_q : q.val = q'.val := by grind
        have h_q' := LtVal q'
        have h_r' := LtVal r'
        simp at h_r'
        simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_q h_q'
        rw [GetFlatten.eq.Get.of.Eq_AddMul h_q'r']
        unfold Tensor.rotate
        simp [GetElem.getElem]
        repeat rw [GetCast.eq.Get.of.Eq.Lt.fin]
        ·
          let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q
          let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_q'
          let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
          let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
          repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
          repeat rw [GetTranspose.eq.Get.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          apply congrArg
          simp
          rw [EqMin.of.Ge h]
          simp [Drop.eq.Nil.of.Ge_Length h]
          simp [EqTake.of.Ge_Length h]
          simp [h_r, h_r']
          simp at h_qₐ_div h_qₑ_div h_rₐ_mod h_rₑ_mod
          rw [EqMin.of.Ge h] at h_qₐ_div h_rₐ_mod
          simp [EqTake.of.Ge_Length h] at h_qₐ_div h_rₐ_mod
          have h_eq_q' : qₐ.val = qₑ.val := by grind
          simp [h_eq_q']
          left
          grind
        ·
          exact h_q'
        ·
          rw [MulProdS.eq.ProdAppend]
          rw [Rotate.eq.AppendDrop__Take]
        ·
          exact h_q
        ·
          rw [MulProdS.eq.ProdAppend]
          rw [Rotate.eq.AppendDrop__Take]
      ·
        repeat rw [Drop.eq.Nil.of.Ge_Length h]
        simp
        rw [EqTake.of.Ge_Length h]


-- created on 2025-10-29
