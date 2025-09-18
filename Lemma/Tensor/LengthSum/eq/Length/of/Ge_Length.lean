import sympy.tensor.tensor
import Lemma.Tensor.EqSum.of.Ge_Length
import Lemma.Tensor.EqLengthS.of.Eq
import Lemma.Algebra.EqLengthS.of.Eq
open Tensor Algebra


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
  apply EqLengthS.of.Eq this


-- created on 2025-06-24
