import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  [Neg α]
-- given
  (X : Tensor α s) :
-- imply
  (-X).length = X.length := by
-- proof
  cases s <;>
  · 
    simp [Tensor.length]


-- created on 2025-10-08
