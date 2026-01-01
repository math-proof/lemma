import Lemma.Tensor.DataGet.eq.Get.of.EqData_Flatten
import Lemma.Vector.EqFlattenUnflatten
open Tensor Vector


@[main, fin]
private lemma main
-- given
  (X : Tensor α (n :: s))
  (i : Fin n) :
-- imply
  X[i].data = X.data.unflatten[i] :=
-- proof
  DataGet.eq.Get.of.EqData_Flatten (v := X.data.unflatten) (X := X) (by rw [EqFlattenUnflatten]) i


-- created on 2025-11-01
