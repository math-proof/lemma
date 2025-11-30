import Lemma.Bool.EqCast.of.SEq
import Lemma.List.EraseIdx.eq.Cons_EraseIdxTail.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Sum.as.Stack_Sum.of.LtAdd_1Length
import sympy.tensor.stack
open Bool List Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (h : d + 1 < s.length)
  (X : Tensor α s) :
-- imply
  have h_length : s.length > 0 := by linarith
  have := Length.eq.Get_0.of.GtLength_0 h_length X
  X.sum (d + 1) = cast (by rw [EraseIdx.eq.Cons_EraseIdxTail.of.GtLength_0 h_length]) ([i < s[0]] (X[i].sum d)) := by
-- proof
  apply Eq_Cast.of.SEq
  apply Sum.as.Stack_Sum.of.LtAdd_1Length h


-- created on 2025-11-07
