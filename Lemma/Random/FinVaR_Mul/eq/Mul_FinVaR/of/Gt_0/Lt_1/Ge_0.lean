import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.EqFinVaR.of.StrictMono.Lt_1.Ge_0
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {α c : ℝ}
-- given
  (h₀ : 0 ≤ α)
  (h₁ : α < 1)
  (h₂ : 0 < c)
  (X : Ω → ℝ) :
-- imply
  finVaR μ (fun ω => c * X ω) α = c * finVaR μ X α := by
-- proof
  exact Random.EqFinVaR.of.StrictMono.Lt_1.Ge_0 (f := (c * ·)) h₀ h₁ (fun _ _ h => mul_lt_mul_of_pos_left h h₂) X


-- created on 2026-09-26
