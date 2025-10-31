import stdlib.SEq
import sympy.Basic
import sympy.tensor.functions


@[main]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α s) :
-- imply
  (X.permuteHead (d + 1)).sum (d) ≃ X.sum 0 := by
-- proof
  unfold Tensor.permuteHead
  sorry


-- created on 2025-10-31
