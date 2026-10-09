import sympy.core.mul
import sympy.Basic
import Lemma.Vector.ValCast.eq.Val.of.Eq
open Tensor


@[path]
private lemma main
  [Mul α]
-- given
  (A : Tensor α s)
  (B : Tensor α s')
  (h : (mul_shape s s').prod = 0) :
-- imply
  (A.mul B).data.val = [] := by
-- proof
  unfold mul
  rw [dif_pos h]
  exact Vector.ValCast.eq.Val.of.Eq h.symm List.Vector.nil


-- created on 2026-10-07
