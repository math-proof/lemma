import Lemma.Tensor.EqStack_Get
import Lemma.Tensor.Lt_Length.of.GtLength_0
import sympy.tensor.stack
open Tensor


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  [i < s[0]] X[i]'(Lt_Length.of.GtLength_0 h X i) ≃ X := by
-- proof
  match s with
  | [] =>
    contradiction
  | n :: s =>
    simp
    rw [EqStack_Get]


-- created on 2025-11-11
