import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Get_0.of.Ne_Nil
import Lemma.Tensor.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetSplitAt_1.eq.Cast_GetUnflatten
import Lemma.Vector.Head.eq.Get_0
open Tensor Vector


@[main]
private lemma fin
-- given
  (h_i : i < n)
  (X : Tensor α [n]) :
-- imply
  have h_i : i < X.data.length := by
    simpa
  have h_i' : i < X.length := by
    rw [Length.eq.Get_0.of.Ne_Nil (by simp)]
    simpa
  X.data.get ⟨i, h_i⟩ = (X.get ⟨i, h_i'⟩).data[0] := by
-- proof
  intros
  simp [Tensor.get]
  unfold Tensor.toVector
  simp
  simp only [GetElem.getElem]
  rw [GetCast.eq.Get.of.Eq.Lt.fin (by simpa) (by simp)]
  simp
  rw [GetSplitAt_1.eq.Cast_GetUnflatten.fin]
  rw [Head.eq.Get_0.fin]
  rw [Vector.GetUnflatten.eq.Get_AddMul.fin]
  simp
  rw [Vector.GetCast.eq.Get.of.Eq.fin]
  simp


private lemma main
-- given
  (h_i : i < n)
  (X : Tensor α [n]) :
-- imply
  have : i < X.data.length := by
    simpa
  have : i < X.length := by
    rw [Length.eq.Get_0.of.Ne_Nil (by simp)]
    simpa
  X.data[i] = X[i].data[0] := by
-- proof
  apply fin h_i


-- created on 2025-10-11
