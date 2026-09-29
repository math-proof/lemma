import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  -⌈x⌉ = ⌊-x⌋ := by
-- proof
  exact Int.floor_neg.symm


-- created on 2026-09-27
