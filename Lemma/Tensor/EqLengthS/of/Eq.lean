import stdlib.SEq
import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Ite
open Tensor


@[main]
private lemma main
  {X : Tensor α s}
  {Y : Tensor α s'}
-- given
  (h : X ≃ Y) :
-- imply
  X.length = Y.length := by
-- proof
  simp [SEq] at h
  repeat rw [Length.eq.Ite]
  rw [h.left]


-- created on 2025-06-24
