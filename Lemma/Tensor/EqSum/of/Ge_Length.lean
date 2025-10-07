import sympy.tensor.tensor
import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.EqEraseIdx.of.Ge_Length
import Lemma.Algebra.NotGe.of.Lt
open Algebra List Bool


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
    have h := NotGe.of.Lt h
    contradiction
  ·
    apply SEqCast.of.Eq
    rwa [EqEraseIdx.of.Ge_Length]


-- created on 2025-06-23
-- updated on 2025-09-20
