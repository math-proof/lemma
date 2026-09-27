import sympy.stats.quantile
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
-- given
  (μ : Measure Ω)
  (X : Ω → ℝ)
  (α : ℝ) :
-- imply
  quantile μ X α ⊆ quantileLower μ X α := by
-- proof
  intro q h
  exact ⟨h.le_prob_ge⟩


-- created on 2026-09-26
