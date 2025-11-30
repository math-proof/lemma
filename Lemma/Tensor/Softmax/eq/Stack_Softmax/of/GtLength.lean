import Lemma.Tensor.FromVectorMapToVector.eq.Stack
import Lemma.Tensor.Softmax.eq.FromVectorMap_FunSoftmax.of.GtLength
open Tensor


@[main]
private lemma main
  [Exp α]
  {d : ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α (n :: s)) :
-- imply
  X.softmax (d + 1) = [i < n] (X[i].softmax d) := by
-- proof
  rw [Softmax.eq.FromVectorMap_FunSoftmax.of.GtLength h]
  apply FromVectorMapToVector.eq.Stack id


-- created on 2025-11-30
