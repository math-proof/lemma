import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.IsVaR_FinVaR.of.Lt_1.Ge_0
import Lemma.Random.IsVaR.of.IsVaR
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {α : ℝ}
-- given
  (h₀ : 0 ≤ α)
  (h₁ : α < 1)
  (X : Ω → ℝ)
  (c : ℝ) :
-- imply
  finVaR μ (fun ω => X ω + c) α = finVaR μ X α + c := by
-- proof
  have h₂ := Random.IsVaR_FinVaR.of.Lt_1.Ge_0 (μ := μ) (X := fun ω => X ω + c) h₀ h₁
  have h₃ := Random.IsVaR.of.IsVaR (Random.IsVaR_FinVaR.of.Lt_1.Ge_0 (μ := μ) (X := X) h₀ h₁) c
  exact le_antisymm (h₃.isGreatest.2 h₂.isGreatest.1) (h₂.isGreatest.2 h₃.isGreatest.1)


-- created on 2026-09-26
