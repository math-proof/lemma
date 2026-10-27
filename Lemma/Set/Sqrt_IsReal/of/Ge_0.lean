import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ≥ 0) :
-- imply
  (Real.sqrt x : ℂ) ∈ Set.range Complex.ofReal ∧ Real.sqrt x ^ 2 = x :=
-- proof
  ⟨⟨Real.sqrt x, rfl⟩, Real.sq_sqrt h₀⟩


-- created on 2021-04-11
-- updated on 2026-10-26
