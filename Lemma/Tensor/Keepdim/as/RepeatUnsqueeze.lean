import stdlib.SEq
import sympy.tensor.functions
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.GtLength
import Lemma.List.EqSetInsertIdxEraseIdx.of.GtLength
open List Bool


@[main]
private lemma main
  {d : ℕ}
  {s : List ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α (s.eraseIdx d)) :
-- imply
  X.keepdim ≃ (X.unsqueeze d).repeat s[d] ⟨d, Lt_LengthInsertIdxEraseIdx.of.GtLength h 1⟩ := by
-- proof
  apply SEq.of.EqCast.Eq
  ·
    unfold Tensor.keepdim
    simp [h]
  ·
    simp [EqSetInsertIdxEraseIdx.of.GtLength h]


-- created on 2025-10-03
-- updated on 2025-10-04
