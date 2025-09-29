import sympy.tensor.tensor
import sympy.Basic


@[main]
private lemma main
-- given
  (h : s = [])
  (X : Tensor α s) :
-- imply
  X.length = 0 := by
-- proof
  simp [Tensor.length]
  split
  ·
    rfl
  ·
    contradiction


-- created on 2025-06-24
