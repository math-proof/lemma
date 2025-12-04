import sympy.tensor.functions
import Lemma.List.EqSetInsertIdxEraseIdx.of.GtLength
import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.GtLength
open List


@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (X : Tensor α (s.eraseIdx d)) :
-- imply
  X.keepdim = cast (by simp [EqSetInsertIdxEraseIdx.of.GtLength d.isLt]) ((X.unsqueeze d).repeat s[d] ⟨d, Lt_LengthInsertIdxEraseIdx.of.GtLength d.isLt 1⟩) := by
-- proof
  unfold Tensor.keepdim
  simp [d.isLt]


-- created on 2025-10-09
