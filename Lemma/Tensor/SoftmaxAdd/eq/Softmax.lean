import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  [Exp α]
  -- given
  (X : Tensor α s)
  (δ : α)
  (d : ℕ) :
-- imply
  (X + δ).softmax d = X.softmax d := by
-- proof
  sorry


-- created on 2025-11-30
