import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
-- proof
  exact Real.sin_sq x


-- created on 2020-06-28
