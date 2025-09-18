import sympy.tensor.tensor
import Lemma.Logic.SEqCast.of.Eq
import Lemma.Algebra.EqEraseIdx.of.Ge_Length
open Algebra Logic


@[main]
private lemma main
  [Add α] [Zero α]
  {dim : ℕ}
-- given
  (h : dim ≥ s.length)
  (X : Tensor α s) :
-- imply
  X.sum dim ≃ X := by
-- proof
  unfold Tensor.sum
  split_ifs with h
  ·
    linarith
  ·
    apply SEqCast.of.Eq
    rwa [EqEraseIdx.of.Ge_Length]


-- created on 2025-06-23
