import Mathlib.MeasureTheory.Measure.WithDensity
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {𝕡 : Measure Ω}
  {a : Ω → α}
  {f : α → ENNReal}
-- given
  (hP : PSpace 𝕡 a)
  (hf : Measurable f) :
-- imply
  Expectation (𝕡.map a) f =
    ∫⁻ «a.bvar», f «a.bvar» * 𝕡.prob a «a.bvar» ∂ReferenceMeasure.measure := by
-- proof
  simp only [Expectation]
  have hmp : Measurable (𝕡.prob a) :=
    Measure.measurable_rnDeriv (𝕡.map a) ReferenceMeasure.measure
  rw [PSpace.map_eq_withDensity_density,
    lintegral_withDensity_eq_lintegral_mul _ hmp hf]
  simp only [Pi.mul_apply, mul_comm]


-- created on 2023-03-24
