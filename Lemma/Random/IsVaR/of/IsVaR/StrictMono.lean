import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.IsVaR.is.LeRealLtAndLt_RealLe
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {α v : ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : StrictMono f)
  (h₁ : IsVaR μ X α v) :
-- imply
  IsVaR μ (f ∘ X) α (f v) := by
-- proof
  have e₁ : {ω | (f ∘ X) ω < f v} = {ω | X ω < v} := by
    ext
    simp [h₀.lt_iff_lt]
  have e₂ : {ω | (f ∘ X) ω ≤ f v} = {ω | X ω ≤ v} := by
    ext
    simp [h₀.le_iff_le]
  rw [Random.IsVaR.is.LeRealLtAndLt_RealLe, e₁, e₂]
  exact Random.IsVaR.is.LeRealLtAndLt_RealLe.mp h₁


-- created on 2026-09-26
