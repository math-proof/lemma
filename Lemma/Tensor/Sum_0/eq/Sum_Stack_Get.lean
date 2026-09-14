import Lemma.Tensor.EqStack_Get
import torch.Tensor.sum
open Tensor


@[main, fin]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.sum 0 = ∑ i < n, X[i] := by
-- proof
  erw [EqStack_Get]
  rfl


-- created on 2026-07-21
