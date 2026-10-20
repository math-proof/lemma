import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x > 0) :
-- imply
  (Real.sqrt x : ℂ) ∈ Set.range Complex.ofReal ∧ 0 < Real.sqrt x :=
-- proof
  ⟨⟨Real.sqrt x, rfl⟩, Real.sqrt_pos.mpr h₀⟩


-- created on 2021-04-20
-- updated on 2026-10-17
