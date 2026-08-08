import Lemma.Bool.SEq.is.Eq
import sympy.tensor.Basic
open Bool


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (f : α → β) :
-- imply
  A.map f ≃ B.map f := by
-- proof
  have h_s : s = s' := h.left
  subst h_s
  have h := Eq.of.SEq h
  subst h
  rfl


-- created on 2026-08-08
