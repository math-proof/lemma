import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.arccos x ∈ Set.Icc (0 : ℝ) Real.pi := by
  -- proof
  exact ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩

-- created on 2020-11-30
