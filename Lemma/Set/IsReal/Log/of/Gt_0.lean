import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic


@[path]
private lemma main
  {f : α → ℝ}
  {x : α} :
-- imply
  Real.log (f x) ∈ (Set.univ : Set ℝ) :=
-- proof
  trivial


-- created on 2023-04-17
