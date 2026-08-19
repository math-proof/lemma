import Lemma.Tensor.Unsqueeze.eq.OfVectorMap_FunUnsqueeze
import Lemma.Tensor.OfVectorMapToVector.eq.Stack
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α (n :: s))
  (dim : ℕ) :
-- imply
  X.unsqueeze (dim + 1) = [i < n] (X[i].unsqueeze dim) := by
-- proof
  rw [Unsqueeze.eq.OfVectorMap_FunUnsqueeze]
  apply OfVectorMapToVector.eq.Stack


-- created on 2025-07-13
