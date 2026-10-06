import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import sympy.Basic

open Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Icc 0 1) :
-- imply
  Real.arccos x ∈ Set.Icc 0 (π / 2) :=
-- proof
  ⟨Real.arccos_nonneg x, Real.arccos_le_pi_div_two.mpr h.1⟩


-- created on 2021-09-05
