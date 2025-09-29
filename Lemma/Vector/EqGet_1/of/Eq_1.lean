import stdlib.List.Vector.Basic
import sympy.Basic


@[main]
private lemma main
  [One α]
  {a : List.Vector α n}
-- given
  (h : a = 1)
  (i : Fin n) :
-- imply
  a.get i = 1 := by
-- proof
  rw [h]
  apply List.Vector.get_replicate


-- created on 2025-09-23
