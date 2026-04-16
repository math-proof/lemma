import Lemma.Tensor.SEqPermuteHeadS.of.SEq.Eq
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (h_i : i = i') :
-- imply
  X.permuteHead i ≃ X.permuteHead i' := by
-- proof
  apply Tensor.SEqPermuteHeadS.of.SEq.Eq h_i
  rfl


-- created on 2026-04-16
