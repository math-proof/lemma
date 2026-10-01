import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  |x - y| = -x + y := by
-- proof
  rw [abs_of_nonpos (sub_nonpos.mpr h)]
  ring


-- created on 2019-10-30
