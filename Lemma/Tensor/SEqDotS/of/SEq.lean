import Lemma.Bool.SEq.is.Eq
import sympy.tensor.tensor
open Bool


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {A : Tensor α s_A}
  {B : Tensor α s_B}
-- given
  (h : A ≃ B)
  (X : Tensor α s_X) :
-- imply
  A @ X ≃ B @ X := by
-- proof
  have h_s := h.left
  subst h_s
  have h := Eq.of.SEq h
  subst h
  rfl


-- created on 2026-01-13
