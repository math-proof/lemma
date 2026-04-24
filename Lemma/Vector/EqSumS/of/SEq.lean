import Lemma.Vector.EqValS.of.SEq
import sympy.vector.vector
open Vector


@[main]
private lemma main
  [Add α] [Zero α]
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h : a ≃ b) :
-- imply
  a.sum = b.sum := by
-- proof
  have h := EqValS.of.SEq h
  cases a
  cases b
  unfold List.Vector.sum
  simp_all


-- created on 2026-04-24
