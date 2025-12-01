import Lemma.Bool.SEq.is.Eq
import Lemma.Vector.EqMulS.of.Eq
open Bool Vector


@[main]
private lemma main
  [Mul α]
  {x : List.Vector α n}
  {y : List.Vector α n'}
-- given
  (h : x ≃ y)
  (a : α) :
-- imply
  x * a ≃ y * a := by
-- proof
  have h_n := h.left
  subst h_n
  apply SEq.of.Eq
  apply EqMulS.of.Eq
  apply Eq.of.SEq h


-- created on 2025-12-01
