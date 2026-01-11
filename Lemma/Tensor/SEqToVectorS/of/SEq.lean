import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import sympy.tensor.tensor
open Bool


@[main]
private lemma main
  {A : Tensor α (n :: s)}
  {B : Tensor α (n' :: s)}
-- given
  (h : A ≃ B) :
-- imply
  A.toVector ≃ B.toVector := by
-- proof
  unfold Tensor.toVector
  have h_n := h.left
  simp at h_n
  apply SEqCastS.of.SEq.Eq.Eq (by simp)
  simp
  subst h_n
  have h := Eq.of.SEq h
  subst h
  rfl


-- created on 2026-01-11
