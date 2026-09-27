import sympy.stats.quantile
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}
-- given
  (X : Ω → ℝ)
  (α q c : ℝ) :
-- imply
  IsQuantileLower μ X α q ↔ IsQuantileLower μ (fun ω => X ω + c) α (q + c) := by
-- proof
  have e : {ω | q + c ≤ X ω + c} = {ω | q ≤ X ω} := by
    ext
    simp
  exact ⟨fun ⟨h⟩ => ⟨e ▸ h⟩, fun ⟨h⟩ => ⟨e ▸ h⟩⟩


-- created on 2026-09-26
