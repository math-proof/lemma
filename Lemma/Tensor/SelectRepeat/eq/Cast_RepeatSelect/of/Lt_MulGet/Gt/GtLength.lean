import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Gt
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.GtLength
import Lemma.Tensor.SelectRepeat.as.RepeatSelect.of.Lt_MulGet.Gt.GtLength
open Bool List Tensor


@[main]
private lemma main
-- given
  (h_k : s.length > k)
  (h_d : k > d)
  (h_i : i < s[d])
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.repeat n ⟨k, h_k⟩).select ⟨d, by grind⟩ ⟨i, by grind⟩ = cast (by simp [EraseIdxSet.eq.SetEraseIdx.of.Gt h_d, GetEraseIdx.eq.Get.of.Lt.GtLength h_k h_d]) ((X.select ⟨d, by grind⟩ ⟨i, h_i⟩).repeat n ⟨k - 1, by grind⟩) := by
-- proof
  apply Eq_Cast.of.SEq.Eq
  ·
    simp [EraseIdxSet.eq.SetEraseIdx.of.Gt h_d, GetEraseIdx.eq.Get.of.Lt.GtLength h_k h_d]
  ·
    apply SelectRepeat.as.RepeatSelect.of.Lt_MulGet.Gt.GtLength _ h_d


-- created on 2025-11-26
