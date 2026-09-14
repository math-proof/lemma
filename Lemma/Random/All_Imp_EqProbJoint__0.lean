import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
import Lemma.Random.All_EqIntegral_ProbJoint.of.PSpace_Joint
open Random MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace 𝕡 (x, y)) :
-- imply
  have := PSpace.of.PSpace_Joint.fst hP
  ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure,
    𝕡.prob x «x.bvar» = 0 →
    ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
      𝕡.prob (x, y) («x.bvar», «y.bvar») = 0 := by
-- proof
  have hsec := All_EqIntegral_ProbJoint.of.PSpace_Joint hP
  refine hsec.mono fun z hz hzero => ?_
  have hmeas : Measurable (fun «y.bvar» => 𝕡.prob (x, y) (z, «y.bvar»)) :=
    (Measure.measurable_rnDeriv _ _).comp (measurable_const.prodMk measurable_id)
  have hint : ∫⁻ «y.bvar», 𝕡.prob (x, y) (z, «y.bvar») ∂ReferenceMeasure.measure = 0 := by
    rw [hz, hzero]
  exact (lintegral_eq_zero_iff hmeas).mp hint


-- created on 2023-03-21
-- updated on 2026-09-13
