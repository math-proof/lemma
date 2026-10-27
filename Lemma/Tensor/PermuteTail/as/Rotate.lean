import Lemma.Tensor.PermuteTail.as.Rotate.of.LeLength
import Notation.Data.Holor.Permute
open Tensor


@[path]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s) :
-- imply
  X.permuteTail s.length ≃ X.rotate (s.length - 1) := by
-- proof
  apply PermuteTail.as.Rotate.of.LeLength
  rfl


-- created on 2025-10-18
