import sympy.core.mul
import sympy.Basic
import Lemma.Tensor.MaxLengthMulShape.eq.MaxMax
open Tensor


@[path]
private lemma main
-- given
  (s s' s'' : List ℕ)
  (i : ℕ) :
-- imply
  wrapFlat (pad1 s'' ((mul_shape s s').length ⊔ s''.length))
      (mul_shape (mul_shape s s') s'') i =
      wrapFlat (pad1 s'' (s.length ⊔ s'.length ⊔ s''.length))
        (mul_shape (mul_shape s s') s'') i := by
-- proof
  rw [MaxLengthMulShape.eq.MaxMax]


-- created on 2026-10-07
