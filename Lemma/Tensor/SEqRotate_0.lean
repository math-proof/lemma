import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.List.ProdNil.eq.One
import Lemma.List.EqRotate_0
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Nat.EqVal_0
open Tensor List Bool Vector Nat Fin


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
    apply SEqCast.of.SEq.Eq (by simp)
    apply SEq.of.All_EqGetS.Eq.fin (by simp)
    intro t
    rw [GetCast.eq.Get.of.Eq.fin (by grind)]
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨t, by grind⟩) (j := ⟨0, by grind⟩) (by grind)]
    apply (GetTranspose.eq.Get.fin (X.data.splitAt 0) ⟨0, by simp⟩ ⟨t, by grind⟩).trans
    have := GetSplitAt.eq.Get_AddMul_ProdDrop.fin (d := 0) X.data ⟨0, by simp⟩ ⟨t, by grind⟩
    simp at this
    assumption


-- created on 2025-10-19
