import stdlib.SEq
import sympy.tensor.tensor
import Lemma.Nat.Gt_0
import Lemma.Tensor.Sum_0.eq.Sum_Get
open Tensor Nat


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (X : Tensor α s)
  (i : Fin s.length) :
-- imply
  X.sum i = ∑ k : Fin s[i], X.select i k := by
-- proof
  have h_length := Gt_0 i
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    rw [Sum_0.eq.Sum_Get]
    rfl


-- created on 2025-11-06
