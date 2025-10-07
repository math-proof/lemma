import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Vector.EqGetRange
open Tensor Vector


@[main]
private lemma fin
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.toVector = (List.Vector.range n).map fun i => X.get i := by
-- proof
  ext i
  simp
  rw [GetToVector.eq.Get.cons.fin]
  rw [EqGetRange.fin]
  simp [GetElem.getElem]


@[main]
private lemma main
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.toVector = (List.Vector.range n).map fun i => X[i] := by
-- proof
  apply fin


-- created on 2025-09-24
