import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Lt
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.Tensor.SelectRepeat.as.RepeatSelect.of.Lt
open Bool List Tensor


@[main]
private lemma main
  {d : Fin s.length}
  {k : ℕ}
-- given
  (h_k : k < d)
  (X : Tensor α s)
  (i : Fin s[d])
  (n : ℕ) :
-- imply
  (X.repeat n ⟨k, by grind⟩).select ⟨d, by grind⟩ ⟨i, by grind⟩ = cast (by simp [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k, GetEraseIdx.eq.Get.of.Gt.GtLength d.isLt h_k]) ((X.select d i).repeat n ⟨k, by grind⟩) := by
-- proof
  apply Eq_Cast.of.SEq.Eq
  ·
    simp [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k, GetEraseIdx.eq.Get.of.Gt.GtLength d.isLt h_k]
  ·
    apply SelectRepeat.as.RepeatSelect.of.Lt h_k


-- created on 2025-11-26
