import stdlib.List
import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α) :
-- imply
  s.drop s.length = .nil := by
-- proof
  simp_all


-- created on 2025-06-07
-- updated on 2026-07-24
