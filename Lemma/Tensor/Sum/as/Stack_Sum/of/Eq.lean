import Lemma.Tensor.EqStackSUFnGet.of.Eq
import Lemma.Tensor.Sum.eq.Stack_Sum
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (h : n = m)
  (X : Tensor α (n :: s))
  (d : ℕ) :
-- imply
  have : X.length = m := by aesop
  X.sum (d + 1) ≃ [i < m] (X[i].sum d) := by
-- proof
  rw [Sum.eq.Stack_Sum]
  apply EqStackSUFnGet.of.Eq h (·.eraseIdx d) (·.sum d)


-- created on 2025-06-27
-- updated on 2026-07-22
