import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : Ω → ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : Monotone f)
  (x : ℝ) :
-- imply
  μ.real {ω | x ≤ X ω} ≤ μ.real {ω | f x ≤ f (X ω)} := by
-- proof
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro ω hω
  exact h₀ hω


-- created on 2026-09-26
