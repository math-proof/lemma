import sympy.tensor.tensor
import Lemma.Tensor.PermuteTail.as.Rotate.of.LeLength
open Tensor


@[main]
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
