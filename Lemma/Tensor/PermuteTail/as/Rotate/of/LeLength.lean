import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.Nat.Eq.Eq.of.EqAddSMul.Lt.Lt
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.EqGetS
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Nat.Sub.eq.Zero.of.Le
import Lemma.Nat.EqMin.of.Ge
import Lemma.Nat.Mod.eq.Sub
import Lemma.List.ProdAppend.eq.MulProdS
open Vector Nat Tensor Bool List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : n ≥ s.length)
  (X : Tensor α s) :
-- imply
  X.permuteTail n ≃ X.rotate (s.length - 1) := by
-- proof
  simp [Tensor.permuteTail, Tensor.rotate]
  have h_rotate := Rotate.eq.AppendDrop__Take s (s.length - 1)
  have h₀ := Sub.eq.Zero.of.Le h
  have h_min := EqMin.of.Ge h
  apply SEq.of.SEqDataS.Eq
  ·
    simp_all
  ·
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp
    ·
      simp [h_rotate]
    ·
      apply SEq.of.All_EqGetS.Eq
      ·
        intro t
        have h_t := t.isLt
        let ⟨z, t', h_zt⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        simp [GetFlatten.eq.Get.of.Eq_AddMul h_zt]
        have h_z := z.isLt
        simp [h₀] at h_z
        simp [h_z] at ⊢ h_zt
        simp [h₀, h_min] at h_t
        rw [h_rotate, ProdAppend.eq.MulProdS] at h_t
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        rw [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
        simp only [GetElem.getElem]
        rw [GetCast.eq.Get.of.Eq.fin (by simp_all)]
        have h_t' := t'.isLt
        simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_t'
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t'
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
        repeat rw [GetTranspose.eq.Get.fin]
        have h_eq := (h_zt.trans h_q'r').symm.trans h_qr
        simp [h_min, h₀] at h_eq
        have h_r' := r'.isLt
        simp [h_min, h₀] at h_r'
        have h_r := r.isLt
        simp at h_r
        let ⟨h_i, h_j⟩ := Eq.Eq.of.EqAddSMul.Lt.Lt h_r h_r' h_eq
        repeat rw [EqGetS]
        simp [h_i, h_j]
        repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop]
        simp [h₀, h_min]
      ·
        simp [h₀, h_min]
        rw [Mod.eq.Sub] at h_rotate
        simp [h_rotate]


-- created on 2025-10-17
-- updated on 2025-10-18
