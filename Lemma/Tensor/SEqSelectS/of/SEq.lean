import Lemma.Bool.SEq.is.Eq
import sympy.tensor.tensor
open Bool


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
  intro h_s
  have h_s := h_s.symm
  subst h_s
  rw [Eq.of.SEq h]


-- created on 2025-11-28
