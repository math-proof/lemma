import stdlib.SEq
import sympy.Basic
import sympy.vector.vector


@[main]
private lemma main
  [One α]
-- given
  (h : n = n') :
-- imply
  (1 : List.Vector α n) ≃ (1 : List.Vector α n') := by
-- proof
  aesop


-- created on 2025-11-05
