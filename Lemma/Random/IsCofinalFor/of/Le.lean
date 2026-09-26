import sympy.stats.quantile
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {X Y : Ω → ℝ}
-- given
  (h₀ : X ≤ Y)
  (α : ℝ) :
-- imply
  IsCofinalFor (quantileLower μ X α) (quantileLower μ Y α) := by
-- proof
  intro q h
  refine ⟨q, ⟨h.le_prob_ge.trans (measureReal_mono fun ω hω => le_trans hω (h₀ ω))⟩, le_rfl⟩


-- created on 2026-09-26
