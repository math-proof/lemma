import stdlib.SEq
import sympy.vector.vector


@[main]
private lemma main
  [Zero α]
-- given
  (h : n = n') :
-- imply
  (0 : List.Vector α n) ≃ (0 : List.Vector α n') := by
-- proof
  aesop


-- created on 2025-11-05
