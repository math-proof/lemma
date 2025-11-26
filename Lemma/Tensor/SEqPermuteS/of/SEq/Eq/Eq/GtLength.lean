import Lemma.Tensor.SEqPermuteS.of.SEq.GtLength
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_s : s.length > i)
  (h_i : i' = i)
  (h_d : d' = d)
  (h : A ≃ B) :
-- imply
  B.permute ⟨i', by rwa [← h.left, h_i]⟩ d' ≃ A.permute ⟨i, h_s⟩ d:= by
-- proof
  subst h_d h_i
  apply SEq.symm
  apply SEqPermuteS.of.SEq.GtLength h_s h


-- created on 2025-10-19
