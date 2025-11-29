import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Lt
import Lemma.Tensor.SEqRepeatS.of.SEq
import Lemma.Tensor.SelectRepeat.eq.Cast_RepeatSelect.of.Lt
open Bool List Tensor


@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
  {k : ℕ}
-- given
  (h_k : k ≤ d)
  (X : Tensor α s)
  (i : Fin s[d])
  (n : ℕ) :
-- imply
  ((X.unsqueeze k).repeat n ⟨k, by grind⟩).select ⟨d + 1, by grind⟩ ⟨i, by grind⟩ ≃ ((X.select ⟨d, by omega⟩ i).unsqueeze k).repeat n ⟨k, by grind⟩ := by
-- proof
  rw [SelectRepeat.eq.Cast_RepeatSelect.of.Lt (d := ⟨d + 1, by grind⟩) (by grind) (X.unsqueeze k) ⟨i, by grind⟩]
  have h_k_lt : k < d + 1 := by omega
  have h_k_length : s.length ≥ k := by omega
  apply SEqCast.of.SEq.Eq
  ·
    simp [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k_lt]
    simp [EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength h_k_length h_k_lt]
  ·
    apply SEqRepeatS.of.SEq
    sorry


-- created on 2025-11-17
-- updated on 2025-11-29
