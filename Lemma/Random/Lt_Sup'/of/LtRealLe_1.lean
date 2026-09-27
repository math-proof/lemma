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
  {X : Ω → ℝ}
  {t : ℝ}
-- given
  (h₀ : μ.real {ω | X ω ≤ t} < 1) :
-- imply
  t < Finset.univ.sup' Finset.univ_nonempty X := by
-- proof
  by_contra hc
  rw [Set.eq_univ_of_forall (s := {ω | X ω ≤ t}) fun ω => (Finset.le_sup' X (Finset.mem_univ ω)).trans (not_lt.mp hc), probReal_univ] at h₀
  exact lt_irrefl _ h₀


-- created on 2026-09-26
