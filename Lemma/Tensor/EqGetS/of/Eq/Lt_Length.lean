import Lemma.Tensor.EqLengthS.of.SEq
import Lemma.Tensor.EqTFnS.of.Eq.Lt_Length
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
  {i : ℕ}
-- given
  (h₀ : i < A.length)
  (h₁ : A ≃ B) :
-- imply
  have : i < B.length := by rwa [EqLengthS.of.SEq h₁] at h₀
  A[i] ≃ B[i] := by
-- proof
  apply EqTFnS.of.Eq.Lt_Length.tensor h₀ h₁ _ (fun s X i => X.get i)


-- created on 2025-06-29
-- updated on 2025-07-13
