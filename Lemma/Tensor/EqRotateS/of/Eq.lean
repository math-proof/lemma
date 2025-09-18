import Lemma.Tensor.SEqBFnS.of.SEq
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (i : ℕ) :
-- imply
  A.rotate i ≃ B.rotate i := by
-- proof
  apply SEqBFnS.of.SEq h


-- created on 2025-07-13
