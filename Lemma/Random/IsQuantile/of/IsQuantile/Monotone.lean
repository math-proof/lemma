import sympy.stats.quantile
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : Ω → ℝ}
  {α q : ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : Monotone f)
  (h₁ : IsQuantile μ X α q) :
-- imply
  IsQuantile μ (f ∘ X) α (f q) := by
-- proof
  exact ⟨h₁.le_prob_le.trans (measureReal_mono fun ω hω => h₀ hω), h₁.le_prob_ge.trans (measureReal_mono fun ω hω => h₀ hω)⟩


-- created on 2026-09-26
