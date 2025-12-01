import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Nat.EqVal_0
import Lemma.List.EqRotate_Length
open Tensor Bool Vector Nat List Fin


@[main]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  X.rotate s.length ≃ X := by
-- proof
  unfold Tensor.rotate
  apply SEq.of.SEqDataS.Eq
  ·
    apply EqRotate_Length
  ·
    simp
    apply SEqCast.of.SEq.Eq (by simp)
    apply SEq.of.All_EqGetS.Eq
    ·
      intro t
      have h_t := t.isLt
      let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
      simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
      have := GetTranspose.eq.Get (X.data.splitAt (s.length % s.length)) ⟨r, by grind⟩ ⟨q, by grind⟩
      simp at this
      rw [this]
      have := GetSplitAt.eq.Get_AddMul_ProdDrop (d := s.length % s.length) X.data ⟨r, by grind⟩ ⟨q, by grind⟩
      simp at this
      rw [this]
      have h_r := r.isLt
      simp at h_r
      simp [h_r] at h_qr ⊢
      grind
    ·
      simp


-- created on 2025-10-19
