import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Nat.LtVal
open Vector Bool Tensor Nat


@[main]
private lemma main
-- given
  (X : Tensor α [n]) :
-- imply
  X.permuteHead 1 ≃ X := by
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
      have h_t := LtVal t
      simp at h_t
      have := GetFlatten.eq.Get.of.Eq_AddMul (j := ⟨0, by simp⟩) (i := ⟨t, by simpa⟩) (t := t) (by simp) ((⟨X.data.splitAt 1⟩ : Tensor (List.Vector α 1) [n]).rotate 1).data
      simp at this
      simp [this]
      unfold Tensor.rotate
      simp
      simp only [GetElem.getElem]
      repeat rw [GetCast.eq.Get.of.Eq.Lt.fin]
      ·
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (j := ⟨0, by simp⟩) (i := ⟨t, by grind⟩) (t := t) (by grind)]
        rw [GetTranspose.eq.Get.fin]
        repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        simp
      ·
        simpa
      ·
        simp
      ·
        simpa
      ·
        simp


-- created on 2025-10-20
