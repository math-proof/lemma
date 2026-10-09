import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
import Lemma.Random.Map.eq.WithDensityProb
open MeasureTheory Random


@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {x : Ω → α}
-- given
  [SinglePSpace π x] :
-- imply
  ∫⁻ a, π.prob x a ∂ReferenceMeasure.measure = 1 := by
-- proof
  have h := congrArg (fun μ : Measure α => μ Set.univ) (Map.eq.WithDensityProb (π := π) (x := x))
  simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [← h]
  have hP : PSpace π x := ‹SinglePSpace π x›.toPSpace
  have : IsProbabilityMeasure π := hP.toIsProbabilityMeasure
  have : IsProbabilityMeasure (π.map x) := inferInstance
  exact measure_univ


-- created on 2021-08-24
