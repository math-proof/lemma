import sympy.core.mul
open Tensor


@[path]
private lemma main
-- given
  (s s' s'' : List ℕ) :
-- imply
  (mul_shape s s').length ⊔ s''.length =
      s.length ⊔ s'.length ⊔ s''.length := by
-- proof
  rw [mul_shape_length]


-- created on 2026-10-07
