import Lemma.List.GetInsertIdx.eq.Get.of.Lt.GeLength
import Lemma.Tensor.SelectUnsqueeze.as.UnsqueezeSelect.of.Le
open List Tensor


@[main, cast]
private lemma main
  {k d : ℕ}
-- given
  (h_d : d ≤ s.length)
  (h_k : k < d)
  (X : Tensor α s)
  (i : Fin s[d - 1]) :
-- imply
  (X.unsqueeze k).select ⟨d, by grind⟩ ⟨i, by simp [GetInsertIdx.eq.Get.of.Lt.GeLength h_d h_k]⟩ ≃ (X.select ⟨d - 1, by omega⟩ i).unsqueeze k := by
-- proof
  have := SelectUnsqueeze.as.UnsqueezeSelect.of.Le (by grind) X i (k := k) (d := ⟨d - 1, by grind⟩)
  grind


-- created on 2026-07-21
