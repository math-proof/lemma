import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
-- given
  (X : Ω → ℝ)
  (t : ℝ) :
-- imply
  μ.real {ω | X ω < t} + μ.real {ω | t ≤ X ω} = 1 := by
-- proof
  rw [← probReal_add_probReal_compl (μ := μ) (s := {ω | X ω < t}) .of_discrete]
  congr
  ext
  simp


-- created on 2026-09-26
