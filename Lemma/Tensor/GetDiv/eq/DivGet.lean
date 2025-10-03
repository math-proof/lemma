import sympy.tensor.tensor
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetUnflatten.eq.GetSplitAt_1
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.List.Prod.eq.Foldr
open Tensor Vector List


@[main]
private lemma fin
  [Div α]
-- given
  (X : Tensor α (n :: s))
  (A : Tensor α [])
  (i : Fin X.length) :
-- imply
  (X / A).get i = X.get i / A := by
-- proof
  simp [HDiv.hDiv]
  apply Eq.of.EqDataS
  simp [Tensor.get]
  simp [Tensor.toVector]
  simp [GetElem.getElem]
  repeat rw [GetCast.eq.Get.of.Eq.fin (by simp)]
  simp
  repeat rw [GetSplitAt_1.eq.GetUnflatten.fin]
  ext j
  simp
  repeat rw [GetUnflatten.eq.Get_AddMul.fin]
  simp


@[main]
private lemma main
  [Div α]
-- given
  (X : Tensor α (n :: s))
  (A : Tensor α [])
  (i : Fin X.length) :
-- imply
  (X / A)[i] = X[i] / A := by
-- proof
  apply fin


-- created on 2025-09-24
