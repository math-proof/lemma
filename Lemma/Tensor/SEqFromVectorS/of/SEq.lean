import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import sympy.tensor.tensor
open Tensor Bool


@[main]
private lemma main
  {v : List.Vector (Tensor α s) n}
  {v' : List.Vector (Tensor α s) n'}
-- given
  (h : v ≃ v') :
-- imply
  Tensor.fromVector v ≃ Tensor.fromVector v' := by
-- proof
  unfold Tensor.fromVector
  have h_n : n = n' := h.left
  apply SEq.of.SEqDataS.Eq (by simpa)
  simp
  subst h_n
  have h := Eq.of.SEq h
  subst h
  rfl


-- created on 2026-01-11
