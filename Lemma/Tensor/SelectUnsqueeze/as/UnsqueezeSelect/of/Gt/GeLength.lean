import Lemma.List.EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Gt.GtLength
import Lemma.List.GetInsertIdx.eq.Get.of.Gt.GeLength
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import stdlib.SEq
import sympy.tensor.tensor
open List Tensor


@[main]
private lemma main
-- given
  (h_d : s.length ≥ k)
  (h_k : k > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.unsqueeze k).select ⟨d, by grind⟩ ⟨i, by simp [GetInsertIdx.eq.Get.of.Gt.GeLength h_d h_k]⟩ ≃ (X.select ⟨d, by omega⟩ ⟨i, i.isLt⟩).unsqueeze (k - 1) := by
-- proof
  apply SEq.of.SEqDataS.Eq
  ·
    apply EraseIdxInsertIdx.eq.InsertIdxEraseIdx.of.Gt.GtLength (by omega) h_k
  ·
    sorry


-- created on 2025-11-26
