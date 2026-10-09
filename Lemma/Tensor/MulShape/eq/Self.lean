import sympy.core.mul
import sympy.Basic
import Lemma.Tensor.Pad1Length.eq.Self
open Tensor


@[path]
private lemma main
-- given
  (s : List ℕ) :
-- imply
  mul_shape s s = s := by
-- proof
  simp [mul_shape, Pad1Length.eq.Self]


-- created on 2026-10-07
