import sympy.tensor.tensor
import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.ArraySlice.eq.Cast_GetCast_SplitAt_1.of.Lt_Get_0.GtLength_0.Eq_ProdTail.Eq_Prod
import Lemma.Bool.SEqCast.of.SEq.Eq
import Lemma.Bool.SEq.of.Eq
import Lemma.Bool.EqCast.of.Eq
import Lemma.Vector.Eq.of.All_EqGetS
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetArraySlice.eq.Get_Add.of.Lt_Min_Sub
import Lemma.Vector.EqGetMapRange.of.Lt
open Vector Bool


@[main]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  have : (X.unsqueeze 0).length > 0 := by simp [Tensor.length]
  (X.unsqueeze 0)[0] = X := by
-- proof
  unfold Tensor.unsqueeze
  simp
  match X with
  | ⟨data⟩ =>
    simp [GetElem.getElem]
    simp [Tensor.get]
    simp [Tensor.toVector]
    simp [GetElem.getElem]
    apply EqCast.of.SEq
    rw [ArraySlice.eq.Cast_GetCast_SplitAt_1.of.Lt_Get_0.GtLength_0.Eq_ProdTail.Eq_Prod (s := 1 :: s)]
    ·
      apply SEqCast.of.SEq.Eq <;>
        simp
      apply SEq.of.Eq
      unfold List.Vector.splitAt
      simp
      apply Eq.of.All_EqGetS
      intro i
      unfold List.Vector.unflatten
      simp [List.Vector.get]
      rw [GetCast.eq.Get.of.Eq.Lt _ (by simp)]
      rw [GetArraySlice.eq.Get_Add.of.Lt_Min_Sub (by simp)]
      rw [EqGetMapRange.of.Lt] <;>
        simp
      simp only [GetElem.getElem]
      simp [List.Vector.get]
      congr
      apply EqCast.of.Eq
      simp
    repeat simp


@[main]
private lemma fin
-- given
  (X : Tensor α s) :
-- imply
  (X.unsqueeze 0).get ⟨0, by simp [Tensor.length]⟩ = X := by
-- proof
  apply main


-- created on 2025-07-11
