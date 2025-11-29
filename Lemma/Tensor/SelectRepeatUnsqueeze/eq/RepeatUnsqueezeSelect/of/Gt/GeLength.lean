import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Gt.GtLength
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Gt
import Lemma.Tensor.SelectRepeat.eq.Cast_RepeatSelect.of.Gt.GtLength
open Bool Tensor List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_k : s.length ≥ k)
  (h_d : k > d)
  (X : Tensor α s)
  (i : Fin s[d])
  (n : ℕ) :
-- imply
  ((X.unsqueeze k).repeat n ⟨k, by grind⟩).select ⟨d, by grind⟩ ⟨i, by grind⟩ ≃ ((X.select ⟨d, by omega⟩ i).unsqueeze (k - 1)).repeat n ⟨k - 1, by grind⟩ := by
-- proof
  rw [SelectRepeat.eq.Cast_RepeatSelect.of.Gt.GtLength (by grind) h_d (X.unsqueeze k) ⟨i, by grind⟩]
  have h_d_length : s.length > d := by grind
  apply SEqCast.of.SEq.Eq
  ·
    simp [EraseIdxSet.eq.SetEraseIdx.of.Gt h_d]
    simp [EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Gt.GtLength h_d_length h_d 1]
  ·
    sorry


-- created on 2025-11-29
