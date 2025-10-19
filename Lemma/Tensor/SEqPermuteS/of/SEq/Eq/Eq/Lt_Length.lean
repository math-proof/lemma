import Lemma.Tensor.SEqPermuteS.of.SEq.Lt_Length
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_s : dim < s.length)
  (h_dim : dim' = dim)
  (h_k : k' = k)
  (h : A ≃ B) :
-- imply
  B.permute ⟨dim', by rwa [← h.left, h_dim]⟩ k' ≃ A.permute ⟨dim, h_s⟩ k:= by
-- proof
  subst h_k h_dim
  apply SEq.symm
  apply SEqPermuteS.of.SEq.Lt_Length h_s h


-- created on 2025-10-19
