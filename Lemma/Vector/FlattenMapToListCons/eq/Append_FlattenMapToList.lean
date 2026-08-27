import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
-- given
  (head : List.Vector α n)
  (tail : List.Vector (List.Vector α n) m) :
-- imply
  ((head ::ᵥ tail).toList.map List.Vector.toList).flatten = head.toList ++ (tail.toList.map List.Vector.toList).flatten := by
-- proof
  grind [List.Vector.toList_cons]


-- created on 2025-05-08
-- updated on 2026-08-24
