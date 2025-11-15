import Lemma.Tensor.Sum.eq.FromVectorMap_FunSum.of.Lt_Length
import Lemma.Tensor.FromVectorMapToVector.eq.Stack
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (h : d < s.length)
  (X : Tensor α (n :: s)) :
-- imply
  X.sum (d + 1) = [i < n] (X[i].sum d) := by
-- proof
  rw [Sum.eq.FromVectorMap_FunSum.of.Lt_Length h]
  apply FromVectorMapToVector.eq.Stack (fun s => s.eraseIdx d)


-- created on 2025-06-24
-- updated on 2025-07-13
