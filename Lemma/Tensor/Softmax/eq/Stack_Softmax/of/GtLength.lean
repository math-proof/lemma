import Lemma.Tensor.OfVectorMapToVector.eq.Stack
import Lemma.Tensor.Softmax.eq.OfVectorMap_FunSoftmax.of.GtLength
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
  rw [Softmax.eq.OfVectorMap_FunSoftmax.of.GtLength h]
  apply OfVectorMapToVector.eq.Stack id


-- created on 2025-11-30
