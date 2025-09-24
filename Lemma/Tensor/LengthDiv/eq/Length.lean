import sympy.tensor.tensor
import Lemma.Basic


@[main]
private lemma main
  [Div α]
-- given
  (X : Tensor α s)
  (a : Tensor α []) :
-- imply
  (X / a).length = X.length := by
-- proof
  cases s <;>
  ·
    simp [Tensor.length]


-- created on 2025-09-24
