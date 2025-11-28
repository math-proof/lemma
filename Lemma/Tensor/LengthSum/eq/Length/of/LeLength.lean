import Lemma.Tensor.SEqSum.of.LeLength
import Lemma.Tensor.Length.of.SEq
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (h : s.length ≤ d)
  (X : Tensor α s) :
-- imply
  (X.sum d).length = X.length := by
-- proof
  have := SEqSum.of.LeLength h X
  apply Length.of.SEq this


-- created on 2025-06-24
