import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqMin.of.Ge
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Sub.eq.Zero.of.Le
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open List Bool Nat Tensor Vector


@[main]
private lemma main
-- given
  (h : s.length ≤ n)
  (X : Tensor α s) :
-- imply
  X.permuteTail n ≃ X.permuteTail s.length := by
-- proof
  unfold Tensor.permuteTail
  simp
  apply SEq.of.SEqDataS.Eq
  ·
    simp [Sub.eq.Zero.of.Le h]
    rw [EqMin.of.Ge h]
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
        have h_t := t.isLt
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        let ⟨h_q_div, _⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        have h_q := q.isLt
        simp [Sub.eq.Zero.of.Le h] at h_q
        have h_r := r.isLt
        simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
        have h_t : t < (s.take (s.length - s.length)).prod * ((s.drop (s.length - s.length)).rotate (s.length ⊓ s.length - 1)).prod := by
          simp [ProdRotate.eq.Prod] at h_t ⊢
          assumption
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        let ⟨h_q'_div, _⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        simp [ProdRotate.eq.Prod] at h_q_div h_q'_div
        simp [Sub.eq.Zero.of.Le h] at h_q_div
        have h_eq_r : r.val = r'.val := by grind
        have h_q' := q'.isLt
        have h_r' := r'.isLt
        simp at h_q'
        simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_r h_r'
        rw [GetFlatten.eq.Get.of.Eq_AddMul h_q'r']
        unfold Tensor.rotate
        simp [GetElem.getElem]
        repeat rw [GetCast.eq.Get.of.Eq.fin]
        ·
          let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r
          let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_r'
          let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
          let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
          repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
          repeat rw [GetTranspose.eq.Get.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          apply congrArg
          simp [EqMin.of.Ge h]
          simp [Sub.eq.Zero.of.Le h]
          simp [h_q, h_q']
          simp at h_qₐ_div h_qₑ_div h_rₐ_mod h_rₑ_mod
          simp [Sub.eq.Zero.of.Le h] at h_qₐ_div h_rₐ_mod
          simp [EqMin.of.Ge h] at h_qₐ_div h_rₐ_mod
          have h_eq_r' : rₐ.val = rₑ.val := by grind
          simp [h_eq_r']
          grind
        ·
          rw [MulProdS.eq.ProdAppend]
          rw [Rotate.eq.AppendDrop__Take]
        ·
          rw [MulProdS.eq.ProdAppend]
          rw [Rotate.eq.AppendDrop__Take]
      ·
        simp [Sub.eq.Zero.of.Le h]
        simp [EqMin.of.Ge h]


-- created on 2025-10-29
-- updated on 2025-10-30
