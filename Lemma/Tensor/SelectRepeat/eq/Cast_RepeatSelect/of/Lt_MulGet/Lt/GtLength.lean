import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Lt
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.Tensor.SelectRepeat.as.RepeatSelect.of.Lt_MulGet.Lt.GtLength
open Bool List Tensor


@[main]
private lemma main
-- given
  (h_d : s.length > d)
  (h_k : k < d)
  (h_i : i < s[d])
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.repeat n ⟨k, by grind⟩).select ⟨d, by grind⟩ ⟨i, by grind⟩ = cast (by simp [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k, GetEraseIdx.eq.Get.of.Gt.GtLength h_d h_k]) ((X.select ⟨d, h_d⟩ ⟨i, h_i⟩).repeat n ⟨k, by grind⟩) := by
-- proof
  apply Eq_Cast.of.SEq.Eq
  ·
    simp [EraseIdxSet.eq.SetEraseIdx.of.Lt h_k, GetEraseIdx.eq.Get.of.Gt.GtLength h_d h_k]
  ·
    apply SelectRepeat.as.RepeatSelect.of.Lt_MulGet.Lt.GtLength _ h_k


-- created on 2025-11-26
