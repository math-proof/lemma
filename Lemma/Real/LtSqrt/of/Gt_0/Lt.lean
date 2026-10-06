import Mathlib.Analysis.SpecialFunctions.Sqrt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x M : ℝ}
-- given
  (h₀ : x > 0)
  (h₁ : x < M) :
-- imply
  √x < √M := by
-- proof
  exact Real.sqrt_lt_sqrt h₀.le h₁


-- created on 2019-09-12
