import sympy.stats.quantile
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}
-- given
  (X : Ω → ℝ)
  (α q : ℝ) :
-- imply
  IsQuantile μ X α q ↔ IsQuantile μ (-X) (1 - α) (-q) := by
-- proof
  have e₁ : {ω | (-X) ω ≤ -q} = {ω | q ≤ X ω} := by
    ext
    simp
  have e₂ : {ω | -q ≤ (-X) ω} = {ω | X ω ≤ q} := by
    ext
    simp
  constructor
  · intro h
    exact ⟨by rw [e₁]; linarith [h.le_prob_ge], by rw [e₂]; linarith [h.le_prob_le]⟩
  · intro h
    have h₁ := h.le_prob_le
    have h₂ := h.le_prob_ge
    rw [e₁] at h₁
    rw [e₂] at h₂
    exact ⟨by linarith, by linarith⟩


-- created on 2026-09-26
