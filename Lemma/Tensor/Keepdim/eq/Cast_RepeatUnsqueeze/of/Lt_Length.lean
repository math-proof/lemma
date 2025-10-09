import stdlib.SEq
import sympy.tensor.functions
import Lemma.List.EqSetInsertIdxEraseIdx.of.Lt_Length
import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.Lt_Length
open List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : dim < s.length)
  (X : Tensor α (s.eraseIdx dim)) :
-- imply
  X.keepdim = cast (by simp [EqSetInsertIdxEraseIdx.of.Lt_Length h]) ((X.unsqueeze dim).repeat s[dim] ⟨dim, Lt_LengthInsertIdxEraseIdx.of.Lt_Length h 1⟩) := by
-- proof
  unfold Tensor.keepdim
  simp [h]


-- created on 2025-10-09
