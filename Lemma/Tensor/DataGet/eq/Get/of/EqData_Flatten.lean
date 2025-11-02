import sympy.tensor.tensor
import Lemma.Nat.LtVal
import Lemma.Vector.GetMap.eq.FunGet
import Lemma.Vector.GetVal.eq.Get.of.Lt
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten.of.Lt
import Lemma.Vector.EqUnflattenFlatten
open Vector Nat


@[main]
private lemma main
  {v : List.Vector (List.Vector α s.prod) n}
  {X : Tensor α (n :: s)}
-- given
  (h : X.data = v.flatten)
  (i : Fin n) :
-- imply
  X[i].data = v[i] := by
-- proof
  simp [GetElem.getElem]
  simp [Tensor.get]
  have h_i := LtVal i
  simp [Tensor.toVector]
  simp [GetElem.getElem]
  rw [h]
  unfold List.Vector.flatten
  simp [List.Vector.get]
  simp [GetVal.eq.Get.of.Lt (show i.val < v.length by simp)]
  rw [GetCast.eq.Get.of.Eq.Lt (by simp) (by simp)]
  simp [GetElem.getElem]
  rw [GetSplitAt_1.eq.GetUnflatten.of.Lt.fin (by grind)]
  congr
  conv_rhs => rw [Eq_UnflattenFlatten v]
  congr


-- created on 2025-05-26
-- updated on 2025-07-17
