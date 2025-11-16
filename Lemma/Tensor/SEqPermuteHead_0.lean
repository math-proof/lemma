import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.EqGetS
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
open Tensor Vector Bool


@[main]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  X.permuteHead 0 ≃ X := by
-- proof
  unfold Tensor.permuteHead
  apply SEq.of.SEqDataS.Eq
  ·
    simp
  ·
    simp
    apply SEqCast.of.SEq.Eq.Eq
    ·
      simp
    ·
      simp
    ·
      apply SEq.of.All_EqGetS.Eq (by simp)
      intro t
      have h_t := t.isLt
      simp at h_t
      simp [GetFlatten.eq.Get.of.Eq_AddMul (n := s.prod) (m := ([].rotate 1).prod) (i := ⟨0, by simp⟩) (j := ⟨t, by simpa⟩) (t := t) (by simp)]
      unfold Tensor.rotate
      simp
      simp only [GetElem.getElem]
      rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨0, by simp⟩) (j := ⟨0, by simp⟩) (by simp)]
      rw [GetTranspose.eq.Get.fin]
      repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
      simp


-- created on 2025-10-20
