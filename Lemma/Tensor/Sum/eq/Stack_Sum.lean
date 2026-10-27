import Lemma.Tensor.Sum.eq.OfVectorMapToVector
import Lemma.Tensor.OfVectorMapToVector.eq.Stack
import Def.Data.Holor.Sum
open Tensor


@[path]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.sum (d + 1) = [i < n] (X[i].sum d) := by
-- proof
  rw [Sum.eq.OfVectorMapToVector]
  apply OfVectorMapToVector.eq.Stack (·.eraseIdx d)


-- created on 2025-06-24
-- updated on 2026-10-26
