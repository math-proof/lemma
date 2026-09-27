import sympy.stats.quantile
import sympy.Basic
import Lemma.Random.AddRealLtRealGe.eq.One
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {α q : ℝ}
-- given
  (h₀ : α ≤ μ.real {ω | X ω ≤ q})
  (h₁ : μ.real {ω | X ω < q} ≤ α) :
-- imply
  IsQuantile μ X α q := by
-- proof
  exact ⟨h₀, by linarith [Random.AddRealLtRealGe.eq.One (μ := μ) X q]⟩


-- created on 2026-09-26
