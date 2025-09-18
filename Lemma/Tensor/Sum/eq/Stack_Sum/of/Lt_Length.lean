import Lemma.Tensor.Sum.eq.FromVectorToVectorMap.of.Lt_Length
import Lemma.Tensor.FromVectorToVectorMap.eq.Stack
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {dim : ℕ}
-- given
  (h : dim < s.length)
  (X : Tensor α (n :: s)) :
-- imply
  X.sum (dim + 1) = [i < n] (X[i].sum dim) := by
-- proof
  rw [Sum.eq.FromVectorToVectorMap.of.Lt_Length h]
  apply FromVectorToVectorMap.eq.Stack (fun s => s.eraseIdx dim)


-- created on 2025-06-24
-- updated on 2025-07-13
