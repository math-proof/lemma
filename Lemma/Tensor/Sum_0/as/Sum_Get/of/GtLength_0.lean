import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.Sum_0.eq.Sum_Get
import stdlib.SEq
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.sum 0 ≃ ∑ i : Fin s[0], X[i]'(by apply GtLength.of.GtLength_0 h) := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    rw [Sum_0.eq.Sum_Get]
    rfl


@[main]
private lemma fin
  [AddCommMonoid α]
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.sum 0 ≃ ∑ i : Fin s[0], X.get ⟨i, by apply GtLength.of.GtLength_0 h⟩ :=
-- proof
  main h X


-- created on 2025-11-06
