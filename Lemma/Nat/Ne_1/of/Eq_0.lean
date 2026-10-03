import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a : ℝ}
-- given
  (h : a = 0) :
-- imply
  a ≠ 1 := by
-- proof
  rw [h]
  simp


-- created on 2026-10-03
