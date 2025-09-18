import Lemma.Tensor.EqArraySliceSData.of.Eq
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (h₁ : i = i')
  (h₂ : n = n') :
-- imply
  A.data.array_slice i n ≃ B.data.array_slice i' n' := by
-- proof
  rw [h₁]
  rw [h₂]
  apply EqArraySliceSData.of.Eq h


-- created on 2025-06-29
