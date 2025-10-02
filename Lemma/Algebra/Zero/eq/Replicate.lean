import sympy.vector.Basic
import sympy.Basic


@[main]
private lemma main
  [Zero α] :
-- imply
  (0 : List.Vector α n) = List.Vector.replicate n 0 :=
-- proof
  rfl


-- created on 2025-06-22
