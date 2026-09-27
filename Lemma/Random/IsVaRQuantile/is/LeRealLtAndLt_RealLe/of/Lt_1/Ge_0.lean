import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.IsVaR.is.LeRealLtAndLt_RealLe
import Lemma.Random.IsVaRQuantile.is.IsVaR.of.Lt_1.Ge_0
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
  IsVaRQuantile μ X α v ↔ μ.real {ω | X ω < v} ≤ α ∧ α < μ.real {ω | X ω ≤ v} := by
-- proof
  rw [Random.IsVaRQuantile.is.IsVaR.of.Lt_1.Ge_0 h₀ h₁, Random.IsVaR.is.LeRealLtAndLt_RealLe]


-- created on 2026-09-26
