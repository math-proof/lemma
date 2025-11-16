import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.List.EqRotate_0
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Nat.EqVal_0
open Tensor List Bool Vector Nat


@[main]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  X.rotate 0 ≃ X := by
-- proof
  unfold Tensor.rotate
  apply SEq.of.SEqDataS.Eq
  ·
    apply EqRotate_0
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
        have h_t := t.isLt
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
        simp [GetFlatten.eq.Get.of.Eq_AddMul h_qr]
        have := GetTranspose.eq.Get (X.data.splitAt 0) ⟨0, by simp⟩ ⟨q, by simp⟩
        simp at this
        rw [this]
        have := GetSplitAt.eq.Get_AddMul_ProdDrop (d := 0) X.data ⟨0, by simp⟩ ⟨q, by simp⟩
        simp at this
        rw [this]
        grind
      ·
        simp


-- created on 2025-10-19
