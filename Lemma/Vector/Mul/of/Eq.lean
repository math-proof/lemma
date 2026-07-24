import sympy.Basic
import sympy.vector.vector


@[main]
private lemma main
  [Mul α]
  {x y : List.Vector α n}
-- given
  (h : x = y)
  (a : α) :
-- imply
  x * a = y * a := by
-- proof
  rw [h]


-- created on 2025-12-01
