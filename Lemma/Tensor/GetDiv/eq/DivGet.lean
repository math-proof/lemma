import sympy.tensor.tensor
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.List.Prod.eq.Foldr
import Lemma.Vector.GetMap.eq.UFnGet
open Tensor Vector List


@[main, fin]
private lemma main
  [Div α]
-- given
  (X : Tensor α (n :: s))
  (A : Tensor α [])
  (i : Fin n) :
-- imply
  (X / A)[i] = X[i] / A := by
-- proof
  simp [GetElem.getElem]
  simp [HDiv.hDiv]
  apply Eq.of.EqDataS
  simp [Tensor.get]
  simp [Tensor.toVector]
  simp [GetElem.getElem]
  repeat erw [GetCast.eq.Get.of.Eq.fin (by simp)]
  simp
  repeat erw [GetSplitAt_1.eq.GetUnflatten.fin]
  ext j
  erw [Vector.GetMap.eq.UFnGet (i := ⟨j, by grind⟩)]
  repeat erw [GetUnflatten.eq.Get_AddMul.fin]
  erw [Vector.GetMap.eq.UFnGet]


-- created on 2025-09-24
