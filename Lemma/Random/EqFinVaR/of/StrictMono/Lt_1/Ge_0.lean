import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.IsVaR_FinVaR.of.Lt_1.Ge_0
import Lemma.Random.IsVaR.of.IsVaR.StrictMono
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {α : ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : 0 ≤ α)
  (h₁ : α < 1)
  (h₂ : StrictMono f)
  (X : Ω → ℝ) :
-- imply
  finVaR μ (f ∘ X) α = f (finVaR μ X α) := by
-- proof
  have h₃ := Random.IsVaR_FinVaR.of.Lt_1.Ge_0 (μ := μ) (X := f ∘ X) h₀ h₁
  have h₄ := Random.IsVaR.of.IsVaR.StrictMono h₂ (Random.IsVaR_FinVaR.of.Lt_1.Ge_0 (μ := μ) (X := X) h₀ h₁)
  exact le_antisymm (h₄.isGreatest.2 h₃.isGreatest.1) (h₃.isGreatest.2 h₄.isGreatest.1)


-- created on 2026-09-26
