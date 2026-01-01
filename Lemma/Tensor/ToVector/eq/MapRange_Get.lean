import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Vector.EqGetRange
open Tensor Vector


@[main, fin]
private lemma main
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.toVector = (List.Vector.range n).map fun i => X[i] := by
-- proof
  simp [GetElem.getElem]
  ext i
  simp
  rw [GetToVector.eq.Get.cons.fin]
  rw [EqGetRange.fin]


-- created on 2025-09-24
