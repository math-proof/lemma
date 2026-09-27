import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.IsVaR_FinVaR.of.Lt_1.Ge_0
import Lemma.Random.IsQuantile.of.IsVaR
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {α : ℝ}
-- given
  (h₀ : 0 ≤ α)
  (h₁ : α < 1)
  (X : Ω → ℝ) :
-- imply
  (quantile μ X α).Nonempty := by
-- proof
  exact ⟨finVaR μ X α, Random.IsQuantile.of.IsVaR (Random.IsVaR_FinVaR.of.Lt_1.Ge_0 h₀ h₁)⟩


-- created on 2026-09-26
