import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
-- proof
  exact Real.sin_sq x


-- created on 2026-09-27
