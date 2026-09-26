import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.IsQuantile.of.IsVaR
import Lemma.Random.IsCofinalFor.of.Lt_1.Ge_0
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {α v : ℝ}
-- given
  (h₀ : 0 ≤ α)
  (h₁ : α < 1) :
-- imply
  IsVaRQuantile μ X α v ↔ IsVaR μ X α v := by
-- proof
  constructor
  · intro h
    exact ⟨⟨(⟨h.isGreatest.1.le_prob_ge⟩ : IsQuantileLower μ X α v), upperBounds_mono_of_isCofinalFor (Random.IsCofinalFor.of.Lt_1.Ge_0 h₀ h₁ X) h.isGreatest.2⟩⟩
  · intro h
    exact ⟨⟨Random.IsQuantile.of.IsVaR h, upperBounds_mono_of_isCofinalFor (fun q hq => ⟨q, (⟨hq.le_prob_ge⟩ : IsQuantileLower μ X α q), le_rfl⟩) h.isGreatest.2⟩⟩


-- created on 2026-09-26
