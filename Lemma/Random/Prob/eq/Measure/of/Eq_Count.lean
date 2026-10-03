import Lemma.Measure.EqRnDeriv_Count
import sympy.stats.joint_rv
open MeasureTheory Measure


/--
Over a countable discrete state space with counting reference measure, the canonical density of a
random variable at a point is the measure of the corresponding event:
`ℙ(x = v) = π {ω | x ω = v}`.
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [Countable α] [MeasurableSingletonClass α]
  {π : Measure Ω}
  {x : Ω → α}
  [SinglePSpace π x]
-- given
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (v : α) :
-- imply
  ℙ[π](x = v) = π (x ⁻¹' {v}) := by
-- proof
  have hx : AEMeasurable x π := PSpace.aemeasurable
  unfold Measure.prob
  rw [hα, EqRnDeriv_Count (μ := π.map x) v, Measure.map_apply_of_aemeasurable hx (measurableSet_singleton v)]


-- created on 2026-10-02