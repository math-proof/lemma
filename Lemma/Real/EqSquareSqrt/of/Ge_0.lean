import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ≥ 0) :
-- imply
  (√x)² = x :=
-- proof
  Real.sq_sqrt h


-- created on 2025-01-16
