import Lemma.Tensor.EqTFnS.of.Eq.Lt_Length
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (h_dim : dim < s.length)
  (offset : ℕ) :
-- imply
  A.permute ⟨dim, h_dim⟩ offset ≃ B.permute ⟨dim, by rwa [← h.left]⟩ offset := by
-- proof
  apply EqTFnS.of.Eq.Lt_Length h_dim h _ (fun (s : List ℕ) (dim : Fin s.length) (X : Tensor α s) => X.permute dim offset)


-- created on 2025-07-13
