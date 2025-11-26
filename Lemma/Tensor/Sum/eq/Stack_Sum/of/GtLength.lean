import Lemma.Tensor.Sum.eq.FromVectorMap_FunSum.of.GtLength
import Lemma.Tensor.FromVectorMapToVector.eq.Stack
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α (n :: s)) :
-- imply
  X.sum (d + 1) = [i < n] (X[i].sum d) := by
-- proof
  rw [Sum.eq.FromVectorMap_FunSum.of.GtLength h]
  apply FromVectorMapToVector.eq.Stack (fun s => s.eraseIdx d)


-- created on 2025-06-24
-- updated on 2025-07-13
