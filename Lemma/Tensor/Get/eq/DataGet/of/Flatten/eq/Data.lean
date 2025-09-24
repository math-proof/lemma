import sympy.tensor.tensor
import Lemma.Algebra.LtVal
import Lemma.Algebra.GetMap.eq.FunGet
import Lemma.Algebra.GetVal.eq.Get.of.Lt
import Lemma.Tensor.GetCast.eq.Get.of.Eq.Lt
import Lemma.Algebra.GetSplitAt_1.eq.GetUnflatten.of.Lt
import Lemma.Algebra.EqUnflattenFlatten
open Algebra Tensor


@[main]
private lemma main
  {v : List.Vector (List.Vector α s.prod) s₀}
  {t : Tensor α (s₀ :: s)}
-- given
  (h : v.flatten = t.data)
  (i : Fin s₀) :
-- imply
  v[i] = t[i].data := by
-- proof
  simp [GetElem.getElem]
  simp [Tensor.get]
  have h_i := LtVal i
  simp [Tensor.toVector]
  simp [GetElem.getElem]
  simp_all [GetMap.eq.FunGet]
  rw [← h]
  unfold List.Vector.flatten
  simp [List.Vector.get]
  simp [GetVal.eq.Get.of.Lt]
  rw [GetCast.eq.Get.of.Eq.Lt (by simp) (by simp)]
  simp [GetElem.getElem]
  rw [GetSplitAt_1.eq.GetUnflatten.of.Lt.fin]
  congr
  conv in v => rw [Eq_UnflattenFlatten v]
  congr


-- created on 2025-05-26
-- updated on 2025-07-17
