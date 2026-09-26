import sympy.stats.quantile
import sympy.Basic
import Lemma.Random.IsQuantile.of.IsQuantile.Monotone
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : Ω → ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : Monotone f)
  (α : ℝ) :
-- imply
  f '' quantile μ X α ⊆ quantile μ (f ∘ X) α := by
-- proof
  rintro _ ⟨q, hq, rfl⟩
  exact Random.IsQuantile.of.IsQuantile.Monotone h₀ hq


-- created on 2026-09-26
