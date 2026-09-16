import Lemma.Bool.SEqUFnS.of.SEq
import torch.Tensor.Basic
open Bool


@[main]
private lemma main
  [Neg α]
  {X : Tensor α s}
  {Y : Tensor α s'}
-- given
  (h : X ≃ Y) :
-- imply
  -X ≃ -Y := by
-- proof
  apply SEqUFnS.of.SEq h


-- created on 2025-12-04
