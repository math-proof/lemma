import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.LeRealLtAndLt_RealLe.of.Lt_1.Ge_0
import Lemma.Random.IsVaR.is.LeRealLtAndLt_RealLe
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {α : ℝ}
-- given
  (h₀ : 0 ≤ α)
  (h₁ : α < 1) :
-- imply
  IsVaR μ X α (finVaR μ X α) := by
-- proof
  exact Random.IsVaR.is.LeRealLtAndLt_RealLe.mpr (Random.LeRealLtAndLt_RealLe.of.Lt_1.Ge_0 h₀ h₁)


-- created on 2026-09-26
