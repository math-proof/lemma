import Lemma.Bool.SEq.is.Eq
import Lemma.Nat.Eq.of.EqValS
import sympy.tensor.tensor
open Bool Nat


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
  {d : Fin s.length}
  {d' : Fin s'.length}
  {i : Fin s[d]}
  {i' : Fin s'[d']}
-- given
  (h : A ≃ B)
  (h_d : d.val = d'.val)
  (h_i : i.val = i'.val) :
-- imply
  A.select d i ≃ B.select d' i' := by
-- proof
  have h_s := h.left.symm
  have h_s := h_s.symm
  subst h_s
  rw [Eq.of.SEq h]
  have h_d := Eq.of.EqValS h_d
  subst h_d
  have h_i := Eq.of.EqValS h_i
  subst h_i
  rfl


-- created on 2025-11-29
