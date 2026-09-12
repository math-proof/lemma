import Lemma.Random.Integral.ae.Pr.of.Measurable.Measurable.Probability
open MeasureTheory
set_option maxHeartbeats 800000


@[main]
private lemma main
  {Ω α β : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β}
  [JointPSpace 𝕡 x y]
-- given
  (x' : α)
  (h : ∫⁻ y', JointPSpace.density 𝕡 x y (x', y') ∂ReferenceMeasure.measure = 0) :
-- imply
  ∀ᵐ y' ∂ReferenceMeasure.measure, JointPSpace.density 𝕡 x y (x', y') = 0 := by
-- proof
  exact (lintegral_eq_zero_iff
    ((Measure.measurable_rnDeriv _ _).comp (measurable_const.prodMk measurable_id))).mp h


-- created on 2023-03-21
-- updated on 2026-09-12
