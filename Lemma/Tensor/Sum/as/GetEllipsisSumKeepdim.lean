import stdlib.SEq
import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  [Add α] [Zero α]
  {s : List ℕ}
  {dim : Fin s.length}
-- given
  (h : s[dim] > 0)
  (X : Tensor α s) :
-- imply
  X.sum dim ≃ (X.sum_keepdim dim).getEllipsis dim ⟨0, h⟩ := by
-- proof
  unfold Tensor.sum_keepdim
  simp
  sorry


-- created on 2025-10-05
