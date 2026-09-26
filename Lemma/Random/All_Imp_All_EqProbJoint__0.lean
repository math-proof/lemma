import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
import Lemma.Random.All_EqIntegral_ProbJoint.of.PSpace_Joint
import sympy.stats.joint_rv
open Random


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : MeasureTheory.Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace π (x, y)) :
-- imply
  have := PSpace.of.PSpace_Joint.fst hP
  ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure,
    ℙ[π](x = «x.bvar») = 0 →
    ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
      ℙ[π](x = «x.bvar» ∧ y = «y.bvar») = 0 := by
-- proof
  refine (All_EqIntegral_ProbJoint.of.PSpace_Joint hP).mono fun z hz hzero => ?_
  apply (MeasureTheory.lintegral_eq_zero_iff (f := fun «y.bvar» => π.prob (x, y) (z, «y.bvar»)) ((MeasureTheory.Measure.measurable_rnDeriv _ _).comp (measurable_const.prodMk measurable_id))).mp
  rw [hz, hzero]


-- created on 2023-03-21
-- updated on 2026-09-26
