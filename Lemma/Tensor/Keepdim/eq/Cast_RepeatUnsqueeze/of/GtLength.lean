import sympy.tensor.functions
import Lemma.List.EqSetInsertIdxEraseIdx.of.GtLength
import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.GtLength
open List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > dim)
  (X : Tensor α (s.eraseIdx dim)) :
-- imply
  X.keepdim = cast (by simp [EqSetInsertIdxEraseIdx.of.GtLength h]) ((X.unsqueeze dim).repeat s[dim] ⟨dim, Lt_LengthInsertIdxEraseIdx.of.GtLength h 1⟩) := by
-- proof
  unfold Tensor.keepdim
  simp [h]


-- created on 2025-10-09
