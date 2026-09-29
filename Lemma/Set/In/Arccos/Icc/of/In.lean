import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {e a b : ℝ}
-- given
  (h : e ∈ Set.Icc a b) :
-- imply
  Real.arccos e ∈ Set.Icc (Real.arccos b) (Real.arccos a) := by
-- proof
  exact ⟨Real.arccos_le_arccos h.2, Real.arccos_le_arccos h.1⟩


-- created on 2026-09-27
