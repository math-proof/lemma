import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
import Lemma.Random.Map.eq.WithDensityProb
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω} {a : Ω → α} {f : α → ENNReal}
-- given
  (hP : SinglePSpace π a)
  (hf : Measurable f) :
-- imply
  𝔼[a: π](f a) =
    ∫⁻ «a.bvar», f «a.bvar» * ℙ[π](a = «a.bvar») ∂ReferenceMeasure.measure := by
-- proof
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_ennreal]
  have hmp : Measurable (π.prob a) :=
    Measure.measurable_rnDeriv (π.map a) ReferenceMeasure.measure
  rw [Random.Map.eq.WithDensityProb,
    lintegral_withDensity_eq_lintegral_mul _ hmp hf]
  simp only [Pi.mul_apply, mul_comm]


-- created on 2023-03-24
-- updated on 2026-09-20
