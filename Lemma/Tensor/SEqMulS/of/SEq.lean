import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.EqMulS.of.Eq
open Bool Tensor


@[main]
private lemma main
  [Mul α]
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (a : α) :
-- imply
  A * a ≃ B * a := by
-- proof
  have h_n := h.left
  subst h_n
  apply SEq.of.Eq
  apply EqMulS.of.Eq
  apply Eq.of.SEq h


-- created on 2025-12-01
