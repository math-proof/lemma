import sympy.vector.Basic
import sympy.Basic


@[main]
private lemma main
  [Zero α]
  {a : List.Vector α n}
-- given
  (h : a = 0)
  (i : Fin n) :
-- imply
  a.get i = 0 := by
-- proof
  rw [h]
  apply List.Vector.get_replicate


-- created on 2025-09-23
