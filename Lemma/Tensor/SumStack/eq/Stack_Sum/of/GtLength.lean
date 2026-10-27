import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetSum.as.SumGet.of.GtGet_0.LtAdd_1Length
import Def.Data.Holor.Stack.Part2
import Def.Data.Holor.Sum
open Bool Tensor
set_option maxHeartbeats 200000


@[path]
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
  rw [EqGetStack]
  apply Eq.of.SEq
  have := GetSum.as.SumGet.of.GtGet_0.LtAdd_1Length (i := i) (d := d) (by simpa) (by simp) ([k < n] f k)
  apply this.trans
  simp [GetElem.getElem]
  erw [EqGetStack.fin]
  rfl


-- created on 2025-11-15
