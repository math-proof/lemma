import sympy.core.mul
import sympy.Basic
open Tensor


@[main]
private lemma main
-- given
  (s s' s'' : List ℕ) :
-- imply
  (mul_shape s s').length ⊔ s''.length =
      s.length ⊔ s'.length ⊔ s''.length := by
-- proof
  rw [mul_shape_length]


-- created on 2026-10-07
