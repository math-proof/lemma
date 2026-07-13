import sympy.tensor.tensor
import Lemma.Nat.Eq_0.of.Lt_1
import Lemma.Tensor.EqLengthUnsqueeze_0'1
import Lemma.Bool.EqCast.of.Eq
import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.Unsqueeze.eq.TensorMap_FunGetData
import Lemma.Vector.ArraySlice.as.GetCast_SplitAt_1.of.GtGet_0.GtLength_0.Eq_ProdTail.Eq_Prod
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.EqGetMapRange
import Lemma.Vector.GetArraySlice.eq.Get_Add.of.Lt_Min_Sub
import Lemma.Vector.GetCast.eq.Get.of.Eq
open Bool Nat Vector Tensor


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
  rw [ArraySlice.eq.Cast_GetCast_SplitAt_1.of.GtGet_0.GtLength_0.Eq_ProdTail.Eq_Prod (s := 1 :: s) _ (by grind)]
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


@[main, fin]
private lemma nat
-- given
  (X : Tensor α s)
  (z : Fin ((X.unsqueeze 0).length)) :
-- imply
  (X.unsqueeze 0)[z]'(by grind) = X := by
-- proof
  have h_z := z.isLt
  simp only [Tensor.EqLengthUnsqueeze_0'1] at h_z
  have h_z := Eq_0.of.Lt_1 h_z
  have h_z := Fin.Eq_Fin.of.EqVal h_z
  simp [h_z]
  have := main X
  aesop

-- created on 2025-07-11
-- updated on 2025-11-30
