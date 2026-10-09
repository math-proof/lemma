import sympy.core.mul
import sympy.Basic
import Lemma.Tensor.Max_LengthMulShape.eq.MaxMax
open Tensor


@[path]
private lemma main
-- given
  (s s' s'' : List ℕ)
  (i : ℕ) :
-- imply
  wrapFlat (pad1 s (s.length ⊔ (mul_shape s' s'').length))
      (mul_shape s (mul_shape s' s'')) i =
      wrapFlat (pad1 s (s.length ⊔ s'.length ⊔ s''.length))
        (mul_shape s (mul_shape s' s'')) i := by
-- proof
  rw [Max_LengthMulShape.eq.MaxMax]


-- created on 2026-10-07
