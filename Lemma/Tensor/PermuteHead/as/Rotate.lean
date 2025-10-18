import sympy.tensor.tensor
import Lemma.Tensor.PermuteHead.as.Rotate.of.Ge_Length
open Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s) :
-- imply
  X.permuteHead s.length ≃ X.rotate 1 := by
-- proof
  apply PermuteHead.as.Rotate.of.Ge_Length
  rfl


-- created on 2025-10-18
