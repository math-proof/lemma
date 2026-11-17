import Lemma.Random.IsVaR.is.LeRealLtAndLt_RealLe
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
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
-- updated on 2026-11-17
