import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetSum.as.SumGet.of.Lt_Get_0.LtAdd_1Length
import sympy.tensor.stack
open Bool Tensor
set_option maxHeartbeats 400000


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (h : s.length > d)
  (f : Fin n → Tensor α s):
-- imply
  ([k < n] f k).sum (d + 1) = [k < n] (f k).sum d := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGetStack.fn]
  apply Eq.of.SEq
  have := GetSum.as.SumGet.of.Lt_Get_0.LtAdd_1Length (i := i) (d := d) (by simpa) (by simp) ([k < n] f k)
  apply SEq.trans this
  simp [GetElem.getElem]
  rw [EqGetStack.fn.fin]


-- created on 2025-11-15
