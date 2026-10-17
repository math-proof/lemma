import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ≥ 0) :
-- imply
  (Real.sqrt x : ℂ) ∈ Set.range Complex.ofReal ∧ Real.sqrt x ^ 2 = x :=
-- proof
  ⟨⟨Real.sqrt x, rfl⟩, Real.sq_sqrt h₀⟩


-- created on 2026-10-11
-- updated on 2026-10-17
