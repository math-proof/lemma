import stdlib.List
import sympy.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : i ≥ a.length) :
-- imply
  a.drop i = .nil := by
-- proof
  simp_all


-- created on 2025-06-07
