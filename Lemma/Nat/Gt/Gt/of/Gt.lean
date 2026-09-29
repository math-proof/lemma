import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y b : ℝ}
-- given
  (h : x > max y b) :
-- imply
  x > y ∧ x > b := by
-- proof
  exact max_lt_iff.mp h


-- created on 2026-09-27
