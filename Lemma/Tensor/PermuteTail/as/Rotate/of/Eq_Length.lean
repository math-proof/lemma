import Lemma.Tensor.PermuteTail.as.Rotate
import torch.Tensor.permute
open Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : n = s.length)
  (X : Tensor α s) :
-- imply
  X.permuteTail n ≃ X.rotate (n - 1) := by
-- proof
  subst h
  apply PermuteTail.as.Rotate


-- created on 2025-10-18
