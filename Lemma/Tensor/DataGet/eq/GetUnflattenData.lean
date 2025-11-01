import Lemma.Tensor.DataGet.eq.Get.of.EqData_Flatten
import Lemma.Vector.EqFlattenUnflatten
open Tensor Vector


@[main]
private lemma main
-- given
  (X : Tensor α (n :: s))
  (i : Fin n) :
-- imply
  X[i].data = X.data.unflatten[i] :=
-- proof
  DataGet.eq.Get.of.EqData_Flatten (v := X.data.unflatten) (X := X) (by rw [EqFlattenUnflatten]) i


@[main]
private lemma fin
-- given
  (X : Tensor α (n :: s))
  (i : Fin n) :
-- imply
  (X.get i).data = X.data.unflatten.get i :=
-- proof
  main X i


-- created on 2025-11-01
