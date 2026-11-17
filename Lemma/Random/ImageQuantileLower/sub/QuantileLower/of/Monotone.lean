import Lemma.Random.IsQuantileLower.of.IsQuantileLower.Monotone
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : Ω → ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : Monotone f)
  (α : ℝ) :
-- imply
  f '' quantileLower μ X α ⊆ quantileLower μ (f ∘ X) α := by
-- proof
  rintro _ ⟨q, hq, rfl⟩
  exact Random.IsQuantileLower.of.IsQuantileLower.Monotone h₀ hq


-- created on 2026-09-26
-- updated on 2026-11-17
