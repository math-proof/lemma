import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {X Y : Ω → ℝ}
  {t₁ t₂ : ℝ}
-- given
  (h₀ : X ≤ Y)
  (h₁ : t₁ ≤ t₂) :
-- imply
  μ.real {ω | t₂ < X ω} ≤ μ.real {ω | t₁ < Y ω} := by
-- proof
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro ω hω
  exact h₁.trans_lt (hω.trans_le (h₀ ω))


-- created on 2026-09-26
