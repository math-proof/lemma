import sympy.tensor.tensor
import Lemma.Tensor.EqSum.of.LeLength
import Lemma.Tensor.EqLengthS.of.SEq
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {dim : ℕ}
-- given
  (h : dim ≥ s.length)
  (X : Tensor α s) :
-- imply
  (X.sum dim).length = X.length := by
-- proof
  have := EqSum.of.LeLength h X
  apply EqLengthS.of.SEq this


-- created on 2025-06-24
