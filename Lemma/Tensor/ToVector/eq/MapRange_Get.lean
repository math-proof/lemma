import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Vector.EqGetRange
import Lemma.Vector.GetMap.eq.UFnGet
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
  erw [GetMap.eq.UFnGet]
  simp
  show (toVector X).get i = X.get ((List.Vector.range n).get i)
  erw [GetToVector.eq.Get.cons.fin]
  erw [EqGetRange.fin]


-- created on 2025-09-24
