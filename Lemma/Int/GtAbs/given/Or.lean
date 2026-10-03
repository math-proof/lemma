import sympy.sets.sets
import sympy.Basic
import Lemma.Int.GtAbs.is.Or


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h : |x| > a) :
-- imply
  x < -a ∨ x > a := by
-- proof
  exact Int.GtAbs.is.Or.mp h


-- created on 2026-10-03
