import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
  {s : List.Vector α n}
-- given
  (h: s.val is constant) :
-- imply
  s is constant := by
-- proof
  exact h


-- created on 2024-07-01
