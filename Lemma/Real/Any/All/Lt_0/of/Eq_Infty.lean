import sympy.concrete.quantifier
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic
open Set Filter


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (h : Tendsto f (nhdsWithin x₀ {x₀}ᶜ) atBot) :
-- imply
  ∃ δ > 0, ∀ x | |x - x₀| ∈ Ioo 0 δ, f x < 0 := by
-- proof
  sorry


-- created on 2026-10-11
