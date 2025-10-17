import sympy.tensor.tensor
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.Nat.Eq.Eq.of.EqAddSMul.Lt.Lt
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.EqGetS
import Lemma.Nat.LtVal
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Nat.Sub.eq.Zero.of.Le
import Lemma.Nat.EqMin.of.Ge
import Lemma.Nat.Mod.eq.Sub_1
open Tensor Bool List Vector Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : n ≥ s.length)
  (X : Tensor α s) :
-- imply
  X.permuteTail n ≃ X.rotate (s.length - 1) := by
-- proof
  unfold Tensor.permuteTail Tensor.rotate
  simp
  have h_rotate := Rotate.eq.AppendDrop__Take s (s.length - 1)
  have h₀ := Sub.eq.Zero.of.Le h
  have h_min := EqMin.of.Ge h
  split_ifs with h_s? h_nil h_nil'
  ·
    apply SEq_Cast.of.SEq.Eq
    ·
      simp_all
    ·
      apply SEq.of.SEqDataS.Eq
      ·
        simp_all
      ·
        apply SEqCast.of.SEq.Eq
        ·
          simp_all
        ·
          subst h_nil
          simp_all [DataCast.eq.Cast_Data.of.Eq]
          apply SEq.of.All_EqGetS.Eq (by simp)
          intro t
          have h_t := LtVal t
          simp at h_t
          simp [h_t]
          rw [GetFlatten.eq.Get.of.Eq_AddMul (i := ⟨0, by simp⟩) (j := ⟨0, by simp⟩) (by simp)]
          simp [GetElem.getElem]
          rw [GetCast.eq.Get.of.Eq.fin (by simp)]
          simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  ·
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
        simp [h₀] at h_s?
        grind
  ·
    grind
  ·
    apply SEq.of.SEqDataS.Eq
    ·
      simp_all
    ·
      apply SEqCast.of.SEq.Eq.Eq
      ·
        simp
      ·
        simp_all
      ·
        apply SEq_Cast.of.SEq.Eq
        ·
          simp_all
        ·
          apply SEq.of.All_EqGetS.Eq
          ·
            intro t
            have h_t := LtVal t
            let ⟨z, t', h_zt⟩ := Any_EqAddMul.of.Lt_Mul h_t
            simp [GetFlatten.eq.Get.of.Eq_AddMul h_zt.symm]
            have h_z := LtVal z
            simp [h₀] at h_z
            simp [h_z] at ⊢ h_zt
            simp [h₀, h_min] at h_t
            rw [h_rotate, ProdAppend.eq.MulProdS] at h_t
            let ⟨i, j, h_ij⟩ := Any_EqAddMul.of.Lt_Mul h_t
            rw [GetFlatten.eq.Get.of.Eq_AddMul h_ij.symm]
            simp only [GetElem.getElem]
            rw [Vector.GetCast.eq.Get.of.Eq.fin (by simp_all)]
            have h_t' := LtVal t'
            simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_t'
            let ⟨i', j', h_ij'⟩ := Any_EqAddMul.of.Lt_Mul h_t'
            rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_ij'.symm]
            repeat rw [GetTranspose.eq.Get.fin]
            have h_eq := (h_ij'.trans h_zt).trans h_ij.symm
            simp [h_min, h₀] at h_eq
            have h_j' := LtVal j'
            simp [h_min, h₀] at h_j'
            have h_j := LtVal j
            simp at h_j
            let ⟨h_i, h_j⟩ := Eq.Eq.of.EqAddSMul.Lt.Lt h_j h_j' h_eq
            repeat rw [Vector.EqGetS]
            simp [h_i, h_j]
            repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop]
            simp [h₀, h_min]
          ·
            simp [h₀, h_min]
            rw [Mod.eq.Sub_1] at h_rotate
            simp [h_rotate]


-- created on 2025-10-17
