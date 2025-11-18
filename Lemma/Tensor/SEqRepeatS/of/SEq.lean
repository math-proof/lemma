import Lemma.Tensor.SEqRepeatS.of.SEq.EqValS.Eq
open Tensor


@[main]
private lemma main
  {X : Tensor α s}
  {X' : Tensor α s'}
-- given
  (h : X ≃ X')
  (n : ℕ)
  (d : Fin s.length):
-- imply
  have h_s := h.left.symm
  X.repeat n d ≃ X'.repeat n ⟨d, by simp [h_s]⟩ :=
-- proof
  SEqRepeatS.of.SEq.EqValS.Eq rfl (by simp) h

-- created on 2025-11-18
