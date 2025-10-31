import Lemma.Tensor.SEqSumS.of.SEq
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_i : i = i')
  (h : A ≃ B) :
-- imply
  A.sum i ≃ B.sum i' := by
-- proof
  subst h_i
  apply SEqSumS.of.SEq h


-- created on 2025-10-31
