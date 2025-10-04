import stdlib.SEq
import sympy.tensor.functions
import Lemma.Logic.SEq.of.EqCast.Eq
import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.Lt_Length
import Lemma.List.EqSetInsertIdxEraseIdx.of.Lt_Length
open Logic List


@[main]
private lemma main
  [Add α] [Zero α]
  {dim : ℕ}
-- given
  (X : Tensor α s)
  (h : dim < s.length) :
-- imply
  X.sum_keepdim dim ≃ ((X.sum dim).unsqueeze dim).repeat s[dim] ⟨dim, Lt_LengthInsertIdxEraseIdx.of.Lt_Length h 1⟩ := by
-- proof
  apply SEq.of.EqCast.Eq
  · 
    unfold Tensor.sum_keepdim
    simp [h]
  · 
    simp [EqSetInsertIdxEraseIdx.of.Lt_Length h]


-- created on 2025-10-03
-- updated on 2025-10-04
