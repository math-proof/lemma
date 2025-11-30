import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetSoftmax.eq.SoftmaxGet.of.Lt_Get_0.LtAdd_1Length
import sympy.tensor.stack
open Bool Tensor


@[main]
private lemma main
  [Exp α]
-- given
  (h : s.length > d)
  (f : Fin n → Tensor α s) :
-- imply
  ([k < n] f k).softmax (d + 1) = [k < n] (f k).softmax d := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGetStack.fn]
  apply Eq.of.SEq
  simp [GetSoftmax.eq.SoftmaxGet.of.Lt_Get_0.LtAdd_1Length (i := i) (d := d) (by simpa) (by simp) ([k < n] f k)]
  simp [GetElem.getElem]
  rw [EqGetStack.fn.fin]


-- created on 2025-11-30
