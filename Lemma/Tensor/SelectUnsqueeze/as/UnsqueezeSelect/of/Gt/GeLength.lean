import Lemma.List.GetInsertIdx.eq.Get.of.Gt.GeLength
import stdlib.SEq
import sympy.tensor.tensor
open List


@[main]
private lemma main
-- given
  (h_d : k ≤ s.length)
  (h_k : k > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.unsqueeze k).select ⟨d, by grind⟩ ⟨i, by simp [GetInsertIdx.eq.Get.of.Gt.GeLength h_d h_k]⟩ ≃ (X.select ⟨d, by omega⟩ ⟨i, i.isLt⟩).unsqueeze (k - 1) := by
-- proof
  sorry


-- created on 2025-11-26
