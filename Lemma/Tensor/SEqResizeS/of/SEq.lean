import Lemma.Tensor.SEqResizeS.of.SEq.EqValS.Eq
open Tensor


@[main]
private lemma main
  [Zero α]
  {X : Tensor α s}
  {X' : Tensor α s'}
-- given
  (h : X ≃ X')
  (d : Fin s.length)
  (n : ℕ) :
-- imply
  have h_s := h.left.symm
  X.resize d n ≃ X'.resize ⟨d, by simp [h_s]⟩ n :=
-- proof
  SEqResizeS.of.SEq.EqValS.Eq rfl (by simp) h


-- created on 2026-07-10
