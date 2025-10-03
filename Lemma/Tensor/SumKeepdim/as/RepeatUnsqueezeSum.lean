import stdlib.SEq
import sympy.tensor.functions
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
import Lemma.Algebra.Le_Sub_1.of.Lt
import Lemma.Algebra.EqAdd_Sub.of.Lt
open List Algebra


@[main]
private lemma main
  [Add α] [Zero α]
  {dim : ℕ}
-- given
  (X : Tensor α s)
  (h_dim : dim < s.length) :
-- imply
  have h_dim : dim < ((s.eraseIdx dim).insertIdx dim 1).length := by
    rw [List.LengthInsertIdx.eq.Add1Length.of.Le_Length] <;>
      rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length h_dim]
    .
      rwa [EqAdd_Sub.of.Ge]
      apply Algebra.Ge_1.of.Gt h_dim
    .
      apply Le_Sub_1.of.Lt h_dim
  X.sum_keepdim dim ≃ ((X.sum dim).unsqueeze dim).repeat s[dim] ⟨dim, h_dim⟩ := by
-- proof
  sorry


-- created on 2025-10-03
