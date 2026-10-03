import Lemma.Random.All_NeProb_0.All_NeProb_0.of.All_Ne0ProbJoint
import sympy.Basic
open Random MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω} {x : Ω → α} {y : Ω → β}
-- given
  (hP : SinglePSpace π (x, y))
  (h : ∀ᵐ z ∂(ReferenceMeasure.measure : Measure (α × β)), ℙ[π](x = z.1 ∧ y = z.2) ≠ 0) :
-- imply
  have := PSpace.of.PSpace_Joint.fst hP
  ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure, ℙ[π](x = «x.bvar») ≠ 0 := by
-- proof
  exact (All_NeProb_0.All_NeProb_0.of.All_Ne0ProbJoint hP h).left


-- created on 2026-10-02
