import Lemma.Tensor.SEqBFnS.of.SEq
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (i j : ℕ) :
-- imply
  A.transpose i j ≃ B.transpose i j := by
-- proof
  apply SEqBFnS.of.SEq h


-- created on 2025-07-13
