import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.Sum_0.eq.Sum_Stack_Get
open Tensor


@[main, fin, cast, cast.fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.sum 0 ≃ ∑ i < s[0], X[i]'(GtLength.of.GtLength_0 h X i) := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    rw [Sum_0.eq.Sum_Stack_Get]
    rfl


-- created on 2026-07-21
-- updated on 2026-07-22
