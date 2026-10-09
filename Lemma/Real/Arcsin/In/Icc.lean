import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.arcsin x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  -- proof
  exact ⟨Real.neg_pi_div_two_le_arcsin x, Real.arcsin_le_pi_div_two x⟩

-- created on 2023-10-03
