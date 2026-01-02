import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.Sum_0.eq.Sum_Get
import stdlib.SEq
import sympy.tensor.tensor
open Tensor


@[main, fin]
private lemma main
  [AddCommMonoid α]
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.sum 0 ≃ ∑ i : Fin s[0], X[i]'(GtLength.of.GtLength_0 h X i) := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    rw [Sum_0.eq.Sum_Get]
    rfl


-- created on 2025-11-06
