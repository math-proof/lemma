import Lemma.Tensor.Length.of.SEq
import Lemma.Tensor.EqTFnS.of.Eq.GtLength
open Tensor


@[main, fin]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
  {i : ℕ}
-- given
  (h₀ : A.length > i)
  (h₁ : A ≃ B) :
-- imply
  A[i] ≃ B[i]'(by rwa [Length.of.SEq h₁] at h₀) := by
-- proof
  apply EqTFnS.of.Eq.GtLength.tensor h₀ h₁ _ (fun s X i => X.get i)


-- created on 2025-06-29
-- updated on 2025-07-13
