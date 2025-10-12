import stdlib.SEq
import sympy.tensor.functions
import Lemma.List.LengthPermute.eq.Length
open List


@[main]
private lemma main
  [ExpPos α]
-- given
  (h : dim < s.length - 1)
  (X : Tensor α s) :
-- imply
  X.softmax dim ≃ (X.permute ⟨dim, by omega⟩ (s.length - 1 - dim)).softmax.permute ⟨s.length - 1, by simp [LengthPermute.eq.Length]; omega⟩ (dim + 1 - s.length) := by
-- proof
  sorry


-- created on 2025-10-12
