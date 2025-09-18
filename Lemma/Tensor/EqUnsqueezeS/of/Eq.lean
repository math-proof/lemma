import Lemma.Tensor.SEqBFnS.of.SEq
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (d : ℕ) :
-- imply
  A.unsqueeze d ≃ B.unsqueeze d := by
-- proof
  apply SEqBFnS.of.SEq h


-- created on 2025-07-13
