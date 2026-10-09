import sympy.functions.elementary.trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
-- given
  (x : ℝ) :
-- imply
  Real.sin x ∈ Set.Icc (-1) 1 := by
-- proof
  exact ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩


-- created on 2023-10-03
