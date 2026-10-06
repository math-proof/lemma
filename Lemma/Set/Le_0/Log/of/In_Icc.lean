import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {y : ℝ}
-- given
  (h : y ∈ Set.Ioc 0 1) :
-- imply
  Real.log y ≤ 0 :=
-- proof
  Real.log_nonpos h.1.le h.2


-- created on 2023-04-17
-- updated on 2025-04-20
