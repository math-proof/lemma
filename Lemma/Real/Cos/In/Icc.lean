import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.cos x ∈ Set.Icc (-1 : ℝ) 1 := by
  -- proof
  exact ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩

-- created on 2023-11-26
