import sympy.tensor.tensor
import Lemma.Bool.EqCast.of.Eq
import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.Unsqueeze.eq.TensorMap_FunGetData
import Lemma.Vector.ArraySlice.eq.Cast_GetCast_SplitAt_1.of.Lt_Get_0.GtLength_0.Eq_ProdTail.Eq_Prod
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.EqGetMapRange
import Lemma.Vector.GetArraySlice.eq.Get_Add.of.Lt_Min_Sub
import Lemma.Vector.GetCast.eq.Get.of.Eq
open Bool Vector Tensor


@[main, fin]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  (X.unsqueeze 0)[0]'(by grind) = X := by
-- proof
  simp [Unsqueeze.eq.TensorMap_FunGetData]
  cases X
  simp [GetElem.getElem]
  simp [Tensor.get]
  simp [Tensor.toVector]
  simp [GetElem.getElem]
  apply EqCast.of.SEq
  rw [ArraySlice.eq.Cast_GetCast_SplitAt_1.of.Lt_Get_0.GtLength_0.Eq_ProdTail.Eq_Prod (s := 1 :: s) _ (by grind)]
  apply SEqCast.of.SEq.Eq <;>
    simp
  apply SEq.of.Eq
  unfold List.Vector.splitAt
  simp
  apply Eq.of.All_EqGetS
  intro i
  unfold List.Vector.unflatten
  simp [List.Vector.get]
  simp only [GetElem.getElem]
  simp [GetCast.eq.Get.of.Eq.fin]
  rw [GetArraySlice.eq.Get_Add.of.Lt_Min_Sub.fin (by simp)]
  rw [EqGetMapRange.fin]
  simp only [GetElem.getElem]
  simp [List.Vector.get]
  congr
  apply EqCast.of.Eq
  repeat simp


-- created on 2025-07-11
-- updated on 2025-11-30
