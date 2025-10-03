import stdlib.SEq
import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  [Add α] [Zero α]
  {dim : ℕ}
-- given
  (X : Tensor α s)
  (h_dim : dim < s.length) :
-- imply
  have h_dim : dim < ((s.eraseIdx dim).insertIdx dim 1).length := by
    sorry
  X.sum_keepdim dim ≃ ((X.sum dim).unsqueeze dim).repeat s[dim] ⟨dim, h_dim⟩ := by
-- proof
  sorry


-- created on 2025-10-03
