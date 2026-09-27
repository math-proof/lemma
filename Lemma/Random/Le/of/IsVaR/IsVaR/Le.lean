import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.IsCofinalFor.of.Le
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {X Y : Ω → ℝ}
  {α v₁ v₂ : ℝ}
-- given
  (h₀ : X ≤ Y)
  (h₁ : IsVaR μ X α v₁)
  (h₂ : IsVaR μ Y α v₂) :
-- imply
  v₁ ≤ v₂ := by
-- proof
  exact upperBounds_mono_of_isCofinalFor (Random.IsCofinalFor.of.Le h₀ α) h₂.isGreatest.2 h₁.isGreatest.1


-- created on 2026-09-26
