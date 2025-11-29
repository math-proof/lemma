import Lemma.Finset.Sum.of.All_Eq
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.Sum_0.eq.Sum_Get
import Lemma.Vector.Sum.eq.Sum_Get
import sympy.tensor.tensor
open Finset Tensor Vector


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.sum 0 = X.toVector.sum := by
-- proof
  rw [Sum.eq.Sum_Get]
  simp [GetElem.getElem]
  have h_all := GetToVector.eq.Get.cons.fin X
  rw [Sum.of.All_Eq.fin h_all]
  rw [Sum_0.eq.Sum_Get.fin]


-- created on 2025-11-01
