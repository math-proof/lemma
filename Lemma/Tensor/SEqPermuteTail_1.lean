import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
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
    apply SEqCast.of.SEq.Eq (by simp)
    apply SEq.of.All_EqGetS.Eq (by simp)
    intro t
    have h_t := t.isLt
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
    have h_r := r.isLt
    simp at h_r
    simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
    unfold Tensor.rotate
    simp [GetElem.getElem]
    rw [GetCast.eq.Get.of.Eq.fin]
    .
      rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (j := ⟨0, by simp⟩) (i := ⟨r, by simpa⟩) (t := r) (by simp)]
      rw [GetTranspose.eq.Get.fin]
      repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
      simp
      simp at h_qr
      aesop
    .
      simp


-- created on 2025-10-20
