import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.Ne_Nil
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetSplitAt_1.eq.Cast_GetUnflatten
import Lemma.Vector.Head.eq.Get_0
import sympy.tensor.tensor
open Tensor Vector


@[main, fin]
private lemma main
-- given
  (h_s : s.length > 0)
  (h_i : s.prod > i)
  (X : Tensor α s) :
-- imply
  -- have := GtLength.of.GtLength_0 (by grind) X ⟨i, by grind⟩
  have h_i_div : i / s.tail.prod < X.length := by
    sorry
  have h_i_mod : i % s.tail.prod < s.tail.prod := by
    sorry
  X.data[i]'(by simpa) = X[i / s.tail.prod].data[i % s.tail.prod] := by
-- proof
  simp [GetElem.getElem]
  intros
  simp [Tensor.get]
  unfold Tensor.toVector
  simp [GetElem.getElem]
  simp [GetCast.eq.Get.of.Eq.fin]
  rw [GetSplitAt_1.eq.Cast_GetUnflatten.fin]
  rw [Head.eq.Get_0.fin]
  rw [Vector.GetUnflatten.eq.Get_AddMul.fin],simp [GetCast.eq.Get.of.Eq.fin]


-- created on 2026-04-08
