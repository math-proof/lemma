import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Get_0.of.Ne_Nil
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Vector.GetSplitAt_1.eq.Cast_GetUnflatten
import Lemma.Vector.Head.eq.Get_0
open Tensor Vector


@[main]
private lemma fin
-- given
  (h_i : i < n)
  (X : Tensor α [n]) :
-- imply
  X.data.get ⟨i, by simpa⟩ = (X.get ⟨i, GtLength.of.GtLength_0 (by grind) X ⟨i, by grind⟩⟩).data[0] := by
-- proof
  intros
  simp [Tensor.get]
  unfold Tensor.toVector
  simp [GetElem.getElem]
  simp [GetCast.eq.Get.of.Eq.fin]
  rw [GetSplitAt_1.eq.Cast_GetUnflatten.fin]
  rw [Head.eq.Get_0.fin]
  rw [Vector.GetUnflatten.eq.Get_AddMul.fin]
  simp [GetCast.eq.Get.of.Eq.fin]


@[main]
private lemma main
-- given
  (h_i : i < n)
  (X : Tensor α [n]) :
-- imply
  have := GtLength.of.GtLength_0 (by grind) X ⟨i, by grind⟩
  X.data[i]'(by simpa) = X[i].data[0] :=
-- proof
  fin h_i X


-- created on 2025-10-11
