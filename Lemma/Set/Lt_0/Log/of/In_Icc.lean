import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ∈ Ioo 0 1) :
-- imply
  Real.log x < 0 :=
-- proof
  Real.log_neg h₀.1 h₀.2


-- created on 2026-09-26
