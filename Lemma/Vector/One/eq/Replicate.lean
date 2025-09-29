import stdlib.List.Vector.Basic
import sympy.Basic


@[main]
private lemma main
  [One α] :
-- imply
  (1 : List.Vector α n) = List.Vector.replicate n 1 :=
-- proof
  rfl


-- created on 2025-09-22
