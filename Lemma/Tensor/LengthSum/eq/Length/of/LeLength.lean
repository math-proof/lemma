import sympy.tensor.tensor
import Lemma.Tensor.EqSum.of.LeLength
import Lemma.Tensor.Length.of.SEq
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {dim : ℕ}
-- given
  (h : s.length ≤ dim)
  (X : Tensor α s) :
-- imply
  (X.sum dim).length = X.length := by
-- proof
  have := EqSum.of.LeLength h X
  apply Length.of.SEq this


-- created on 2025-06-24
