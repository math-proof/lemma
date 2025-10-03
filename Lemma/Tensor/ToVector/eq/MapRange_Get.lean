import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Vector.EqGetRange
open Tensor Vector


@[main]
private lemma fin
-- given
  (v : Tensor α (n :: s)) :
-- imply
  v.toVector = (List.Vector.range n).map fun i => v.get i := by
-- proof
  ext i
  simp
  rw [GetToVector.eq.Get.fin]
  rw [EqGetRange.fin]
  simp [GetElem.getElem]


@[main]
private lemma main
-- given
  (v : Tensor α (n :: s)) :
-- imply
  v.toVector = (List.Vector.range n).map fun i => v[i] := by
-- proof
  apply fin


-- created on 2025-09-24
