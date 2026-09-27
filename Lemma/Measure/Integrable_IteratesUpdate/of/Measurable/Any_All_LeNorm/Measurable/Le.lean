import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Lemma.Measure.Measurable_IteratesUpdate.of.Measurable.Measurable.Le
open MeasureTheory Finset Preorder Measure


@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace Z]
  {n m : ℕ}
  {φ : Z × S → EuclideanVec d}
  {φ₁ : (Iic n → S) → Z}
  {μ : Measure (ℕ → S)} [IsFiniteMeasure μ]
-- given
  (h₀ : n ≤ m)
  (h₁ : Measurable φ)
  (h₂ : ∃ C, ∀ (ω : ℕ → S) s, ‖φ (φ₁ (frestrictLe n ω), s)‖ ≤ C)
  (h₃ : Measurable φ₁) :
-- imply
  Integrable (iterates_update h₀ φ φ₁) μ := by
-- proof
  obtain ⟨C, hC⟩ := h₂
  apply Integrable.of_bound (Measurable_IteratesUpdate.of.Measurable.Measurable.Le h₀ h₁ h₃).aestronglyMeasurable C (ae_of_all _ fun ω => hC ω (ω m))


-- created on 2026-09-26