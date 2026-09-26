import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.IsVaR.is.LeRealLtAndLt_RealLe
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {α v : ℝ}
-- given
  (h₀ : IsVaR μ X α v) :
-- imply
  IsQuantile μ X α v := by
-- proof
  exact ⟨(Random.IsVaR.is.LeRealLtAndLt_RealLe.mp h₀).2.le, h₀.isGreatest.1.le_prob_ge⟩


-- created on 2026-09-26
