import Lemma.Tensor.ToVector.eq.MapRange_Get
import Lemma.Algebra.EqGetRange
import Lemma.Tensor.GetDiv.eq.DivGet
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Tensor.Div.eq.Div_Broadcast
open Tensor Algebra Vector


@[main]
private lemma main
  [Div α]
-- given
  (X : Tensor α (n :: s))
  (A : Tensor α []) :
-- imply
  (X / A).toVector = X.toVector / A.broadcast (n :: s).tail (by simp) := by
-- proof
  repeat rw [ToVector.eq.MapRange_Get.fin]
  ext i
  simp
  rw [GetDiv.eq.DivGet.fin (A := A)]
  rw [GetDiv.eq.DivGet.fin (a := A.broadcast s (by simp))]
  simp
  rw [EqGetRange.fin]
  rw [Div.eq.Div_Broadcast]
  simp


-- created on 2025-09-24
