import stdlib.List
import sympy.Basic


@[main]
private lemma main
  {a : List α} :
-- imply
  a.drop a.length = .nil := by
-- proof
  simp_all


-- created on 2025-06-07
