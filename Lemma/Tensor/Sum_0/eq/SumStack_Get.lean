import Lemma.Tensor.EqStack_Get
open Tensor


@[main, fin]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.sum 0 = ∑ i < n, X[i] := by
-- proof
  conv_lhs => rw [← EqStack_Get X]
  rfl


-- created on 2026-07-22
