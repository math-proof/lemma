import Lemma.Vector.SEq.of.EqValS
import sympy.vector.vector
open Vector


@[main]
private lemma main
-- given
  (h_m : m = 0)
  (h_n : n = 0)
  (a : List.Vector α m)
  (b : List.Vector α n) :
-- imply
  a ≃ b := by
-- proof
  subst h_m h_n
  apply SEq.of.EqValS
  aesop


-- created on 2025-11-07
