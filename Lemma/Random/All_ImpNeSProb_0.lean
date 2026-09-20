import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace π (x, y)) :
-- imply
  ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure, ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
    ℙ[π](x = «x.bvar» | y = «y.bvar») ≠ 0 →
      ℙ[π](x = «x.bvar» ∧ y = «y.bvar») ≠ 0 := by
-- proof
  have hzero : ∀ (a : α) (b : β),
      π.prob (x, y) (a, b) = 0 → π.condProb (x, y) (a, b) = 0 := fun a b hz ↦ by
    simp only [Measure.condProb, hz, div_eq_mul_inv, zero_mul]
  exact Filter.Eventually.of_forall fun «x.bvar» ↦
    Filter.Eventually.of_forall fun «y.bvar» hz hprob0 ↦ hz (hzero «x.bvar» «y.bvar» hprob0)


-- created on 2020-12-11
-- updated on 2026-09-20
