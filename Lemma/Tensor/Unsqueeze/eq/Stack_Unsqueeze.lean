import Lemma.Tensor.Unsqueeze.eq.FromVectorMap_FunUnsqueeze
import Lemma.Tensor.FromVectorMapToVector.eq.Stack
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α (n :: s))
  (dim : ℕ) :
-- imply
  X.unsqueeze (dim + 1) = [i < n] (X[i].unsqueeze dim) := by
-- proof
  rw [Unsqueeze.eq.FromVectorMap_FunUnsqueeze]
  apply FromVectorMapToVector.eq.Stack


-- created on 2025-07-13
