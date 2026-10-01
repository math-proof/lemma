import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x < y) :
-- imply
  |x - y| = -x + y := by
-- proof
  rw [abs_of_nonpos (sub_nonpos.mpr h.le)]
  ring


-- created on 2026-09-27
