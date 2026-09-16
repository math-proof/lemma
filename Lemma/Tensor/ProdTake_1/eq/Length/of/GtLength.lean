import torch.Tensor.Basic
import torch.Tensor.prod
import Lemma.Tensor.ProdTake_1.eq.Length.of.GtLength_0
open Tensor


@[main, comm]
private lemma main
  {X : Tensor α s}
-- given
  (h : X.length > i) :
-- imply
  (s.take 1).prod = X.length := by
-- proof
  apply ProdTake_1.eq.Length.of.GtLength_0
  omega


-- created on 2025-10-12
