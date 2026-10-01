import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  (x : ℝ) :
-- imply
  Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := by
-- proof
  exact Real.cos_sq_add_sin_sq x


-- created on 2023-10-03
