import sympy.stats.value_at_risk
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}
  {X : Ω → ℝ}
  {α v : ℝ}
-- given
  (h₀ : IsVaRQuantile μ X α v) :
-- imply
  IsQuantileLower μ X α v := by
-- proof
  exact ⟨h₀.isGreatest.1.le_prob_ge⟩


-- created on 2026-09-26
