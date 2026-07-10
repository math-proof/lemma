import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.GtLength
import Lemma.Bool.SEqCast.of.Eq
import sympy.tensor.functions
open List Bool


@[main, cast]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (X : Tensor α (s.eraseIdx d)) :
-- imply
  X.keepdim ≃ (X.unsqueeze d).repeat ⟨d, Lt_LengthInsertIdxEraseIdx.of.GtLength d.isLt 1⟩ s[d] := by
-- proof
  unfold Tensor.keepdim
  simp [d.isLt]
  apply SEqCast.of.Eq
  simp
  apply EqSetInsertIdxEraseIdx.of.GtLength


-- created on 2025-10-09
