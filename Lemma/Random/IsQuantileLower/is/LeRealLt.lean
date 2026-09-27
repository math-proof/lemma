import sympy.stats.quantile
import sympy.Basic
import Lemma.Random.AddRealLtRealGe.eq.One
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {α q : ℝ} :
-- imply
  IsQuantileLower μ X α q ↔ μ.real {ω | X ω < q} ≤ α := by
-- proof
  have := Random.AddRealLtRealGe.eq.One (μ := μ) X q
  constructor
  · intro h
    linarith [h.le_prob_ge]
  · intro h
    exact ⟨by linarith⟩


-- created on 2026-09-26
