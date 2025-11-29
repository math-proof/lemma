import Lemma.Tensor.SEqSelectS.of.SEq.EqValS.EqValS
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  have h_s := h.left.symm
  A.select d i ≃ B.select ⟨d, by simp [h_s]⟩ ⟨i, by simp [h_s]⟩ := by
-- proof
  apply SEqSelectS.of.SEq.EqValS.EqValS h rfl rfl


-- created on 2025-11-28
-- updated on 2025-11-29
