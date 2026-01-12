import Lemma.Bool.SEq.is.Eq
import sympy.tensor.tensor
open Bool


@[main]
private lemma main
  [Mul α] [Zero α] [Add α]
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_dvd : s.prod ∣ s_A.prod)
  (h_s : s_A = s_B)
  (h : A ≃ B) :
-- imply
  A.broadcast s_A h_dvd ≃ B.broadcast s_B (by rwa [← h_s, ← h.left]) := by
-- proof
  subst h_s
  have h_s' := h.left
  subst h_s'
  have h := Eq.of.SEq h
  subst h
  rfl


-- created on 2026-01-12
