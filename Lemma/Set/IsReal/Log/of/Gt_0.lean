import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic


@[main]
private lemma main
  {f : α → ℝ}
  {x : α}
-- given
  (h : f x > 0) :
-- imply
  Real.log (f x) ∈ (Set.univ : Set ℝ) :=
-- proof
  trivial


-- created on 2026-09-26
