import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Lt
import Lemma.Tensor.SelectRepeat.eq.Cast_RepeatSelect.of.Lt
import stdlib.SEq
import sympy.tensor.tensor
open Bool Tensor List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (h_i : i < s[d - 1])
  (h_k : k < d)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  ((X.unsqueeze k).repeat n ⟨k, by grind⟩).select ⟨d, by grind⟩ ⟨i, by grind⟩ ≃ ((X.select ⟨d - 1, by omega⟩ ⟨i, by simpa⟩).unsqueeze k).repeat n ⟨k, by grind⟩ := by
-- proof
  let s' := s.insertIdx d 1
  let d' : Fin s'.length := ⟨d, by simp [s']; grind⟩
  rw [SelectRepeat.eq.Cast_RepeatSelect.of.Lt (d := ⟨d, by grind⟩) (by omega) (X.unsqueeze k) ⟨i, by grind⟩]
  apply SEqCast.of.SEq.Eq
  ·
    simp [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k]
    simp [EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength (show s.length ≥ k by omega) h_k]
  ·
    sorry


-- created on 2025-11-17
-- updated on 2025-11-29
