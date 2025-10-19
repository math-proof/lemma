import stdlib.SEq
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Nat.LtVal
import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Nat.EqVal_0
import Lemma.List.EqRotate_Length
open Tensor Bool Vector Nat List


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
    apply SEqCast.of.SEq.Eq.Eq
    ·
      simp
    ·
      simp
    ·
      apply SEq.of.All_EqGetS.Eq
      ·
        intro t
        have h_t := LtVal t
        let ⟨k, j, h_kj⟩ := Any_EqAddMul.of.Lt_Mul h_t
        simp [GetFlatten.eq.Get.of.Eq_AddMul h_kj.symm]
        have := GetTranspose.eq.Get (X.data.splitAt (s.length % s.length)) ⟨j, by grind⟩ ⟨k, by grind⟩
        simp at this
        rw [this]
        have := GetSplitAt.eq.Get_AddMul_ProdDrop (d := s.length % s.length) X.data ⟨j, by grind⟩ ⟨k, by grind⟩
        simp at this
        rw [this]
        have h_j := LtVal j
        simp at h_j
        simp [h_j] at h_kj ⊢
        grind
      ·
        simp


-- created on 2025-10-19
