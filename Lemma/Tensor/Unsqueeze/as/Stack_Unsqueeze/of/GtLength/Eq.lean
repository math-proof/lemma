import Lemma.Tensor.Unsqueeze.eq.Stack_Unsqueeze
import Lemma.Tensor.EqStackSUFnGet.of.Eq
open Tensor


@[main]
private lemma main
-- given
  (h : n = m)
  (X : Tensor α (n :: s))
  (dim : ℕ) :
-- imply
  have : X.length = m := by aesop
  X.unsqueeze (dim + 1) ≃ [i < m] (X[i].unsqueeze dim) := by
-- proof
  rw [Unsqueeze.eq.Stack_Unsqueeze]
  apply EqStackSUFnGet.of.Eq h _ (·.unsqueeze dim)


-- created on 2025-07-13
