import Lemma.Vector.EqSumS.of.SEq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetSum.eq.SumMapGet
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import sympy.tensor.tensor
open Vector


@[main, comm]
private lemma main
  [AddCommMonoid α]
-- given
  (X : Tensor α [n]) :
-- imply
  (X.sum 0).data.head = X.data.sum := by
-- proof
  unfold Tensor.sum
  simp
  unfold List.Vector.splitAt
  simp
  rw [Head.eq.Get_0.fin]
  rw [GetSum.eq.SumMapGet.fin]
  rw [EqSumS.of.SEq]
  apply SEq.of.All_EqGetS.Eq.fin
  ·
    intro i
    have h_i := i.isLt
    simp
    rw [Head.eq.Get_0.fin]
    rw [GetUnflatten.eq.Get_AddMul.fin]
    simp
    rw [GetCast.eq.Get.of.Eq.fin (by simp)]
    simp
  ·
    simp


-- created on 2026-04-24
