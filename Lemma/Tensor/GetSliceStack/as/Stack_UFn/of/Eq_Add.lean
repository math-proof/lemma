import Lemma.Tensor.GetSliceStack.as.Stack_UFn
open Tensor


@[main]
private lemma main
  {n k j : ℕ}
-- given
  (h : n = k + j)
  (f : ℕ → Tensor α s) :
-- imply
  ([i < n] f i)[:k] ≃ [i < k] f i := by
-- proof
  rw [h]
  apply GetSliceStack.as.Stack_UFn


-- created on 2026-08-19
