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
  μ.real {ω | X ω ≤ Finset.univ.sup' Finset.univ_nonempty X} = 1 := by
-- proof
  rw [Set.eq_univ_of_forall (s := {ω | X ω ≤ Finset.univ.sup' Finset.univ_nonempty X}) fun ω => Finset.le_sup' X (Finset.mem_univ ω), probReal_univ]


-- created on 2026-09-26
