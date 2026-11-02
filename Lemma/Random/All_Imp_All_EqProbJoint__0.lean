import Lemma.Random.All_EqIntegral_ProbJoint.of.PSpace_Joint
open Random


@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : MeasureTheory.Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : SinglePSpace π (x, y)) :
-- imply
  have := SinglePSpace.of.SinglePSpace.fst hP
  ∀ᵐ «\sf{x}» ∂ReferenceMeasure.measure,
    ℙ[π](x = «\sf{x}») = 0 →
    ∀ᵐ «\sf{y}» ∂ReferenceMeasure.measure,
      ℙ[π](x = «\sf{x}» ∧ y = «\sf{y}») = 0 := by
-- proof
  refine (All_EqIntegral_ProbJoint.of.PSpace_Joint hP).mono fun z hz hzero => ?_
  apply (MeasureTheory.lintegral_eq_zero_iff (f := fun «\sf{y}» => π.prob (x, y) (z, «\sf{y}»)) ((MeasureTheory.Measure.measurable_rnDeriv _ _).comp (measurable_const.prodMk measurable_id))).mp
  rw [hz, hzero]


-- created on 2023-03-21
-- updated on 2026-11-02
