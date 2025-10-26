import Lemma.Tensor.SEqPermuteHeadS.of.SEq
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_i : i = i')
  (h : A ≃ B) :
-- imply
  A.permuteHead i ≃ B.permuteHead i' := by
-- proof
  subst h_i
  apply SEqPermuteHeadS.of.SEq h


-- created on 2025-10-26
