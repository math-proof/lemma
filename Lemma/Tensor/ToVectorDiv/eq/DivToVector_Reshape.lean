import Lemma.Tensor.ToVector.eq.MapRange_Get
import Lemma.Vector.EqGetRange
import Lemma.Tensor.GetDiv.eq.DivGet
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Tensor.Div.eq.Div_Reshape
open Tensor Vector


@[main]
private lemma main
  [Div α]
-- given
  (X : Tensor α (n :: s))
  (A : Tensor α []) :
-- imply
  (X / A).toVector = X.toVector / A.reshape (n :: s).tail (by simp) := by
-- proof
  repeat rw [ToVector.eq.MapRange_Get.fin]
  ext i
  repeat erw [GetMap.eq.UFnGet.fin]
  rw [EqGetRange.fin]
  erw [GetDiv.eq.DivGet.fin (A := A)]
  erw [Div.eq.Div_Reshape]


-- created on 2025-09-24
