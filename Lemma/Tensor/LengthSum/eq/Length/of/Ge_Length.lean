import sympy.tensor.tensor
import Lemma.Tensor.EqSum.of.Ge_Length
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
  have := EqSum.of.Ge_Length h X
  apply EqLengthS.of.SEq this


-- created on 2025-06-24
