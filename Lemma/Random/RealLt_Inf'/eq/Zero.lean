import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Fintype.Basic
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Nonempty Ω]
-- given
  (X : Ω → ℝ) :
-- imply
  μ.real {ω | X ω < Finset.univ.inf' Finset.univ_nonempty X} = 0 := by
-- proof
  rw [Set.eq_empty_of_forall_notMem (s := {ω | X ω < Finset.univ.inf' Finset.univ_nonempty X}) fun ω h => (Finset.inf'_le X (Finset.mem_univ ω)).not_gt h, measureReal_empty]


-- created on 2026-09-26
