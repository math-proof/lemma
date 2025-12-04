import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EqSetInsertIdxEraseIdx.of.GtLength
import Lemma.List.LengthInsertIdxEraseIdx.eq.Length.of.GtLength
import Lemma.List.LengthSet.eq.Length
import Lemma.Tensor.EqSelectRepeatUnsqueeze.of.Lt.GeLength
import Lemma.Tensor.SelectCast.eq.Cast_Select.of.Eq
import sympy.tensor.functions
open Bool List Tensor


@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (X : Tensor α (s.eraseIdx d))
  (i : Fin s[d]) :
-- imply
  X.keepdim.select d i = X := by
-- proof
  unfold Tensor.keepdim
  simp
  have h_length := LengthInsertIdxEraseIdx.eq.Length.of.GtLength d.isLt 1
  have h_set : (((s.eraseIdx d).insertIdx d 1).set d (s[d] * ((s.eraseIdx d).insertIdx d 1)[d])) = s := by 
    simp [EqSetInsertIdxEraseIdx.of.GtLength]
  have := SelectCast.eq.Cast_Select.of.Eq (i := ⟨i, by simp⟩) (d := ⟨d, by rw [LengthSet.eq.Length]; omega⟩) h_set (X := ((X.unsqueeze d).repeat s[d] ⟨d, by simp [h_length]⟩))
  simp at this
  rw [this]
  apply EqCast.of.SEq.Eq
  ·
    simp [EqSetInsertIdxEraseIdx.of.GtLength]
  ·
    apply EqSelectRepeatUnsqueeze.of.Lt.GeLength
    repeat grind


-- created on 2025-12-04
