import sympy.stats.quantile
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}
  {X : Ω → ℝ}
  {α q : ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : StrictMono f) :
-- imply
  IsQuantile μ X α q ↔ IsQuantile μ (f ∘ X) α (f q) := by
-- proof
  have e₁ : {ω | (f ∘ X) ω ≤ f q} = {ω | X ω ≤ q} := by
    ext
    simp [h₀.le_iff_le]
  have e₂ : {ω | f q ≤ (f ∘ X) ω} = {ω | q ≤ X ω} := by
    ext
    simp [h₀.le_iff_le]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨e₁ ▸ h₁, e₂ ▸ h₂⟩, fun ⟨h₁, h₂⟩ => ⟨e₁ ▸ h₁, e₂ ▸ h₂⟩⟩


-- created on 2026-09-26
