import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
-- given
  (i n : ℕ) :
-- imply
  Ico i n = range n \ range i := by
-- proof
  simp_all


-- created on 2025-05-18
