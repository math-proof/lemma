import Lemma.List.GetInsertIdx.eq.Get.of.Lt.Le_Length
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
import stdlib.SEq
import sympy.tensor.tensor
open List


@[main]
private lemma main
-- given
  (h_d : d ≤ s.length)
  (h_k : k < d)
  (X : Tensor α s)
  (i : Fin s[d - 1]) :
-- imply
  (X.unsqueeze k).select ⟨d, by grind⟩ ⟨i, by simp [List.GetInsertIdx.eq.Get.of.Lt.Le_Length h_d h_k]⟩ ≃ (X.select ⟨d - 1, by omega⟩ ⟨i, i.isLt⟩).unsqueeze k := by
-- proof
  sorry


-- created on 2025-11-26
