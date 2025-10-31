import stdlib.SEq
import sympy.Basic
import sympy.tensor.functions


@[main]
private lemma main
  [ExpPos α]
  {i d : ℕ}
-- given
  (h : s.length > i + d)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i, by grind⟩ d).softmax (i + d) ≃ (X.softmax i).permute ⟨i, by grind⟩ d := by
-- proof
  sorry


-- created on 2025-10-31
