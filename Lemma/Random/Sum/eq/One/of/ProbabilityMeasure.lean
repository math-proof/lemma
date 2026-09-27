import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
-- given
  (μ : ProbabilityMeasure ι) :
-- imply
  ∑ i, (μ {i} : ℝ) = 1 := by
-- proof
  have h : ∑ i, ((μ {i} : NNReal) : ENNReal) = 1 := by
    simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
  have h' : ∑ i, (μ {i} : NNReal) = 1 := by exact_mod_cast h
  exact_mod_cast h'


-- created on 2026-09-26
