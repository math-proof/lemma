import stdlib.List
import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : i ≥ s.length) :
-- imply
  s.drop i = .nil := by
-- proof
  simp_all


-- created on 2025-06-07
