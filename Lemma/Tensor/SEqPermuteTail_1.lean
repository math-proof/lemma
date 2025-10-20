import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Nat.LtVal
open Tensor Vector Nat Bool


@[main]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  X.permuteTail 1 ≃ X := by
-- proof
  unfold Tensor.permuteTail
  apply SEq.of.SEqDataS.Eq
  ·
    simp
  ·
    simp
    apply SEqCast.of.SEq.Eq.Eq
    .
      simp
    .
      simp
    .
      apply SEq.of.All_EqGetS.Eq (by simp)
      intro t
      have h_t := LtVal t
      let ⟨k', k, h_k'k⟩ := Any_EqAddMul.of.Lt_Mul h_t
      have h_k := LtVal k
      simp at h_k
      simp [GetFlatten.eq.Get.of.Eq_AddMul h_k'k.symm]
      unfold Tensor.rotate
      simp
      simp only [GetElem.getElem]
      rw [GetCast.eq.Get.of.Eq.Lt.fin]
      .
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (j := ⟨0, by simp⟩) (i := ⟨k, by simpa⟩) (t := k) (by simp)]
        rw [GetTranspose.eq.Get.fin]
        repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        simp
        simp at h_k'k
        aesop
      .
        simpa
      .
        simp


-- created on 2025-10-20
