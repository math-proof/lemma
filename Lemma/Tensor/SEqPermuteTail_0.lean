import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.EqGetS
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.Head.eq.Get_0
open Tensor Vector Bool


@[main]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  X.permuteTail 0 ≃ X := by
-- proof
  unfold Tensor.permuteTail
  apply SEq.of.SEqDataS.Eq
  ·
    simp
  ·
    simp
    apply SEqCast.of.SEq.Eq (by simp)
    apply SEq.of.All_EqGetS.Eq (by simp)
    intro t
    have h_t := t.isLt
    simp at h_t
    simp only [GetElem.getElem]
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨t, by simpa⟩) (j := ⟨0, by simp⟩) (by simp)]
    simp [EqGetS]
    unfold Tensor.rotate
    simp
    simp only [GetElem.getElem]
    rw [Vector.GetCast.eq.Get.of.Eq.fin (by simp)]
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨0, by simp⟩) (j := ⟨0, by simp⟩) (by simp)]
    rw [GetTranspose.eq.Get.fin]
    repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    simp


-- created on 2025-10-20
