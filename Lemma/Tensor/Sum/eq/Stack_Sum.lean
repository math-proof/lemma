import Lemma.Tensor.Sum.eq.FromVectorMapToVector
import Lemma.Tensor.FromVectorMapToVector.eq.Stack
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.sum (d + 1) = [i < n] (X[i].sum d) := by
-- proof
  rw [Sum.eq.FromVectorMapToVector]
  apply FromVectorMapToVector.eq.Stack (·.eraseIdx d)


-- created on 2025-06-24
-- updated on 2025-07-13
