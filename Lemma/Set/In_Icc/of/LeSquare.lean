import Mathlib.Analysis.SpecialFunctions.Sqrt
import Lemma.Set.LeSquare.is.In.Icc
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h : x ^ 2 ≤ a ^ 2) :
-- imply
  x ∈ Set.Icc (-√(a ^ 2)) √(a ^ 2) := by
-- proof
  apply (Set.LeSquare.is.In.Icc (sq_nonneg a)).mp h


-- created on 2023-06-18
