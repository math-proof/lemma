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
  IsQuantileLower μ X α q ↔ IsQuantileLower μ (f ∘ X) α (f q) := by
-- proof
  have e : {ω | f q ≤ (f ∘ X) ω} = {ω | q ≤ X ω} := by
    ext
    simp [h₀.le_iff_le]
  exact ⟨fun ⟨h⟩ => ⟨e ▸ h⟩, fun ⟨h⟩ => ⟨e ▸ h⟩⟩


-- created on 2026-09-26
