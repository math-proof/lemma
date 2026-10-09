import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (_h : x ∈ Set.Icc (-1) 1) :
-- imply
  Real.sqrt (1 - x ^ 2) ≥ 0 := by
-- proof
  exact Real.sqrt_nonneg _


-- created on 2021-03-14
