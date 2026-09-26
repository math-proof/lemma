import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : Ω → ℝ}
  {t q : ℝ}
-- given
  (h₀ : t < q) :
-- imply
  μ.real {ω | X ω ≤ t} ≤ μ.real {ω | X ω < q} := by
-- proof
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro ω hω
  exact lt_of_le_of_lt hω h₀


-- created on 2026-09-26
