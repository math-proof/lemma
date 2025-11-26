import Lemma.List.EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength
import Lemma.List.GetInsertIdx.eq.Get.of.Lt.GeLength
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import stdlib.SEq
import sympy.tensor.tensor
open List Tensor


@[main]
private lemma main
-- given
  (h_d : s.length ≥ d)
  (h_k : k < d)
  (X : Tensor α s)
  (i : Fin s[d - 1]) :
-- imply
  (X.unsqueeze k).select ⟨d, by grind⟩ ⟨i, by simp [GetInsertIdx.eq.Get.of.Lt.GeLength h_d h_k]⟩ ≃ (X.select ⟨d - 1, by omega⟩ ⟨i, i.isLt⟩).unsqueeze k := by
-- proof
  apply SEq.of.SEqDataS.Eq
  ·
    apply EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Lt.GeLength (by omega) h_k
  ·
    sorry


-- created on 2025-11-26
