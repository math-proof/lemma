import sympy.stats.quantile
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}
  {X : Ω → ℝ}
  {α q : ℝ}
-- given
  (h₀ : IsQuantile μ X α q) :
-- imply
  IsQuantileLower μ X α q := by
-- proof
  exact ⟨h₀.le_prob_ge⟩


-- created on 2026-09-26
