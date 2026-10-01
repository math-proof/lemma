import Mathlib.Analysis.SpecialFunctions.Sqrt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a : ℝ}
-- given
  (h₀ : x < √a)
  (h₁ : -√a < x) :
-- imply
  x ^ 2 < a := by
-- proof
  have hs : 0 < √a := by linarith
  have ha : 0 < a := Real.sqrt_pos.mp hs
  have e := Real.sq_sqrt ha.le
  nlinarith


-- created on 2020-01-15
