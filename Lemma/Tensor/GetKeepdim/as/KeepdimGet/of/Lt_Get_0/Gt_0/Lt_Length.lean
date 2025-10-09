import sympy.tensor.functions
import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.Lt_Length
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSum.eq.Length.of.Gt_0
import Lemma.Tensor.Sum.as.Stack_Sum.of.LtAdd_1Length
import Lemma.Tensor.EqGetS.of.Eq.Lt_Length
import Lemma.Tensor.EqGetStack.of.Lt
open Tensor List


@[main]
private lemma main
  {dim i : ℕ}
  {s : List ℕ}
-- given
  (h : dim < s.length)
  (h₁ : dim > 0)
  (h_i : i < s[0])
  (X : Tensor α (s.eraseIdx dim)) :
-- imply
  X.keepdim.get ⟨i, by sorry⟩ ≃ ((X.unsqueeze dim).repeat s[dim] ⟨dim, Lt_LengthInsertIdxEraseIdx.of.Lt_Length h 1⟩).get ⟨i, by sorry⟩ := by
-- proof
  sorry


-- created on 2025-10-09
