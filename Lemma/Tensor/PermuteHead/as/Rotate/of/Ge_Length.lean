import sympy.tensor.tensor
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Vector.FlattenCast.eq.Cast_Flatten.of.Eq.Eq
import Lemma.Vector.EqFlattenUnflatten
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Nat.LtVal
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Nat.Eq.Eq.of.EqAddSMul.Lt.Lt
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
open Tensor Bool List Vector Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : n ≥ s.length)
  (X : Tensor α s) :
-- imply
  X.permuteHead n ≃ X.rotate 1 := by
-- proof
  unfold Tensor.permuteHead Tensor.rotate
  simp
  have h_take := EqTake.of.Ge_Length h
  have h_drop := Drop.eq.Nil.of.Ge_Length h
  have h_rotate := Rotate.eq.AppendDrop__Take s 1
  split_ifs with h_s? h_nil h_nil'
  ·
    apply SEq_Cast.of.SEq.Eq.Eq
    ·
      aesop
    ·
      grind
    ·
      apply SEq.of.SEqDataS.Eq
      ·
        simp_all
      ·
        apply SEqCast.of.SEq.Eq
        ·
          simp_all
        ·
          rw [DataCast.eq.Cast_Data.of.Eq]
          ·
            unfold List.Vector.splitAt
            rw [FlattenCast.eq.Cast_Flatten.of.Eq.Eq (by aesop) rfl]
            simp [EqFlattenUnflatten]
            apply SEqCast.of.SEq.Eq
            ·
              aesop
            ·
              rfl
          ·
            aesop
  ·
    aesop
  ·
    grind
  ·
    apply SEq.of.SEqDataS.Eq
    ·
      simp [h_take, h_drop]
    ·
      apply SEqCastS.of.SEq.Eq.Eq
      ·
        simp
      ·
        simp [h_rotate]
      ·
        rw [FlattenCast.eq.Cast_Flatten.of.Eq.Eq _ rfl]
        ·
          apply SEqCast.of.SEq.Eq
          ·
            simp [h_take, h_drop, h_rotate]
          ·
            apply SEq.of.All_EqGetS.Eq
            ·
              intro t
              have h_t := LtVal t
              simp [h_take, h_drop] at h_t
              let ⟨i, j, h_ij⟩ := Any_EqAddMul.of.Lt_Mul h_t
              simp [GetFlatten.eq.Get.of.Eq_AddMul h_ij.symm]
              have h_t : t < ((s.take n).drop (1 % (s.take n).length)).prod * ((s.take n).take (1 % (s.take n).length)).prod * (s.drop n).prod := by
                simpa [h_take, h_drop]
              let ⟨t', z, h_tz⟩ := Any_EqAddMul.of.Lt_Mul h_t
              rw [GetFlatten.eq.Get.of.Eq_AddMul h_tz.symm]
              have h_z := LtVal z
              simp [h_drop] at h_z
              simp [h_z] at ⊢ h_tz
              simp [h_drop] at h_tz
              have h_t' := LtVal t'
              let ⟨i'', j'', h_ij''⟩ := Any_EqAddMul.of.Lt_Mul h_t'
              rw [GetFlatten.eq.Get.of.Eq_AddMul h_ij''.symm]
              repeat rw [GetTranspose.eq.Get, GetSplitAt.eq.Get_AddMul_ProdDrop]
              have h_eq := (h_ij''.trans h_tz).trans h_ij.symm
              simp [h_take] at h_eq
              have h_j'' := LtVal j''
              simp [h_take] at h_j''
              have h_j := LtVal j
              let ⟨h_i, h_j⟩ := Eq.Eq.of.EqAddSMul.Lt.Lt h_j h_j'' h_eq
              simp [h_i, h_j, h_take]
              rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop]
              simp [h_drop]
            ·
              simp [h_take, h_drop]
        ·
          simp [h_take, h_rotate]


-- created on 2025-10-17
