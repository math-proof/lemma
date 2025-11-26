import Lemma.Tensor.EqTFnS.of.Eq.GtLength
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_dim : dim < s.length)
  (h : A ≃ B)
  (k : ℤ) :
-- imply
  A.permute ⟨dim, h_dim⟩ k ≃ B.permute ⟨dim, by rwa [← h.left]⟩ k := by
-- proof
  apply EqTFnS.of.Eq.GtLength h_dim h _ (fun (s : List ℕ) (dim : Fin s.length) (X : Tensor α s) => X.permute dim k)


-- created on 2025-07-13
